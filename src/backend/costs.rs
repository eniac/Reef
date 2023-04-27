use core::panic;

use crate::dfa::NFA;
use clap::ValueEnum;

static POSEIDON_NUM: usize = 238; // jess took literal measurement and 238 is the real diff

#[derive(Debug, Clone, ValueEnum, Copy)]
pub enum JBatching {
    NaivePolys,
    //Plookup,
    Nlookup,
}

#[derive(Debug, Clone, ValueEnum, Copy)]
pub enum JCommit {
    HashChain,
    Nlookup,
}

pub fn logmn(mn: usize) -> usize {
    match mn {
        1 => 1,
        _ => (mn as f32).log2().ceil() as usize,
    }
}

pub fn accepting_circuit<'a>(dfa: &'a NFA, is_match: Option<(usize, usize)>) -> usize {
    // vanishing selection for final check
    // poly of degree (# final states - 1)
    // (alt, # non final states - 1)
    let cost: usize = 2; //constrain to boolean costs
    match is_match {
        None => cost + dfa.get_non_final_states().len() as usize - 1,
        _ => cost + dfa.get_final_states().len() as usize - 1,
    }
}

pub fn commit_circuit_nohash(
    doc_len: usize,
    batch_size: usize,
    commit_type: JCommit,
    is_match: Option<(usize, usize)>,
) -> usize {
    match commit_type {
        JCommit::HashChain => match is_match {
            None => 0,
            Some((_, end)) if end == doc_len => 0,
            _ => panic!("Cant do hashchain with substring"),
        },
        JCommit::Nlookup => {
            let mn: usize = doc_len;
            let log_mn: usize = logmn(mn);
            let mut cost: usize = 0;

            //Multiplications
            cost += batch_size + 1;

            //Sum-check additions
            cost += log_mn * 2;

            //eq calc
            cost += (batch_size + 1) * (2 * log_mn); //2 actual multiplication and 2 for the subtraction

            //combine eqs
            cost += (batch_size + 1) * (log_mn - 1);

            //horners
            cost += batch_size + 1;

            //mult by Tj
            cost += 1;

            // combine qs (for fiat shamir)
            cost += 1;

            cost
        }
    }
}

fn commit_circuit_hash(
    doc_len: usize,
    batch_size: usize,
    commit_type: JCommit,
    is_match: Option<(usize, usize)>,
) -> usize {
    match commit_type {
        JCommit::HashChain => match is_match {
            None => batch_size * POSEIDON_NUM,
            Some((_, end)) if end == doc_len => batch_size * POSEIDON_NUM,
            _ => panic!("Cant do hashchain with substring"),
        },
        JCommit::Nlookup => {
            let mn: usize = doc_len;
            let log_mn: usize = logmn(mn);
            let mut cost = 0;

            //Sum check poseidon hashes
            cost += log_mn * POSEIDON_NUM;

            //R generation hashes
            cost += POSEIDON_NUM;
            cost
        }
    }
}

pub fn naive_cost_model_nohash<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    // vanishing poly - m * n multiplications + 2 for lookup
    let mut cost = dfa.trans.len() - 1;
    cost *= batch_size;

    cost += accepting_circuit(dfa, is_match);

    cost += commit_circuit_nohash(doc_len, batch_size, commit_type, is_match);

    cost
}

pub fn nlookup_cost_model_nohash<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let mn: usize = dfa.trans.len();
    let log_mn: usize = logmn(mn);
    let mut cost: usize = 0;

    //Multiplications
    cost += batch_size + 1;

    //Sum-check additions
    cost += log_mn * 2;

    //eq calc
    cost += (batch_size + 1) * (2 * log_mn);

    //combine eqs
    cost += (batch_size + 1) * (log_mn - 1);

    //horners
    cost += batch_size + 1;

    //mult by Tj
    cost += 1;

    //v_i creation (for fiat shamir)
    cost += batch_size;

    // combine qs (for fiat shamir)
    cost += 1;

    cost += accepting_circuit(dfa, is_match);

    cost += commit_circuit_nohash(doc_len, batch_size, commit_type, is_match);

    cost
}

pub fn nlookup_cost_model_hash<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let mn: usize = dfa.trans.len();
    let log_mn: usize = logmn(mn);
    let mut cost = nlookup_cost_model_nohash(dfa, batch_size, is_match, doc_len, commit_type);

    //Sum check poseidon hashes
    cost += log_mn * POSEIDON_NUM;

    //R generation hashes
    cost += POSEIDON_NUM;

    cost
}

pub fn full_round_cost_model_nohash<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    lookup_type: JBatching,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let cost = match lookup_type {
        JBatching::NaivePolys => {
            naive_cost_model_nohash(dfa, batch_size, is_match, doc_len, commit_type)
        }
        JBatching::Nlookup => {
            nlookup_cost_model_nohash(dfa, batch_size, is_match, doc_len, commit_type)
        } //        JBatching::Plookup => plookup_cost_model_nohash(dfa, batch_size),
    };
    cost
}

pub fn full_round_cost_model<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    lookup_type: JBatching,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let mut cost = match lookup_type {
        JBatching::NaivePolys => {
            naive_cost_model_nohash(dfa, batch_size, is_match, doc_len, commit_type)
        }
        JBatching::Nlookup => {
            nlookup_cost_model_hash(dfa, batch_size, is_match, doc_len, commit_type)
        } //      JBatching::Plookup => plookup_cost_model_hash(dfa, batch_size),
    };

    cost += commit_circuit_hash(doc_len, batch_size, commit_type, is_match);
    cost
}

pub fn get_folded_cost(cost: usize, doc_len: usize, batch_size: usize) -> usize {
    let folding_size: usize = ((cost as f32) / 128.0).log2().ceil() as usize;
    (cost + 10000) * (2 * (doc_len / batch_size) + folding_size)
}

pub fn opt_cost_model_select_with_commit<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
    commit: JCommit,
) -> (JBatching, JCommit, usize, usize) {
    let mut opt_batching: JBatching = JBatching::NaivePolys;
    let mut cost: usize = full_round_cost_model(
        dfa,
        batch_size,
        JBatching::NaivePolys,
        is_match,
        doc_length,
        commit,
    );

    let nlookup = full_round_cost_model(
        dfa,
        batch_size,
        JBatching::Nlookup,
        is_match,
        doc_length,
        commit,
    );
    if nlookup < cost {
        cost = nlookup;
        opt_batching = JBatching::Nlookup;
    }
    (
        opt_batching,
        commit.clone(),
        batch_size,
        get_folded_cost(cost, doc_length, batch_size),
    )
}

pub fn opt_cost_model_select_with_batch<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
) -> (JBatching, JCommit, usize,usize) {
    let mut opt_batching: JBatching = JBatching::NaivePolys;
    let mut opt_commit: JCommit = JCommit::Nlookup;

    let can_hashcahin: bool = match is_match {
        None => true,
        Some((_, end)) if end == doc_length => true,
        _ => false,
    };

    let mut cost: usize = full_round_cost_model(
        dfa,
        batch_size,
        JBatching::NaivePolys,
        is_match,
        doc_length,
        JCommit::Nlookup,
    );

    let nlookup_with_nlookup = full_round_cost_model(
        dfa,
        batch_size,
        JBatching::Nlookup,
        is_match,
        doc_length,
        JCommit::Nlookup,
    );

    if nlookup_with_nlookup < cost {
        cost = nlookup_with_nlookup;
        opt_batching = JBatching::Nlookup;
        opt_commit = JCommit::Nlookup;
    }

    if can_hashcahin {
        let nlookup_with_hashchain = full_round_cost_model(
            dfa,
            batch_size,
            JBatching::Nlookup,
            is_match,
            doc_length,
            JCommit::HashChain,
        );
        let naive_with_hashchain = full_round_cost_model(
            dfa,
            batch_size,
            JBatching::NaivePolys,
            is_match,
            doc_length,
            JCommit::HashChain,
        );

        if nlookup_with_hashchain < cost {
            cost = nlookup_with_hashchain;
            opt_batching = JBatching::Nlookup;
            opt_commit = JCommit::HashChain;
        }
        if naive_with_hashchain < cost {
            cost = naive_with_hashchain;
            opt_batching = JBatching::NaivePolys;
            opt_commit = JCommit::HashChain;
        }
    }

    let folding_size: usize = ((cost as f32) / 128.0).log2().ceil() as usize;
    (
        opt_batching,
        opt_commit.clone(),
        batch_size,
        get_folded_cost(cost, doc_length, batch_size),
    )
}

pub fn opt_commit_select_with_batch<'a>(
    dfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
    batching: JBatching,
) -> (JBatching, JCommit, usize,usize) {
    let can_hashcahin: bool = match is_match {
        None => true,
        Some((_, end)) if end == doc_length => true,
        _ => false,
    };

    let opt_batching: JBatching = batching;
    let mut opt_commit: JCommit = JCommit::Nlookup;
    let mut cost: usize = full_round_cost_model(
        dfa,
        batch_size,
        opt_batching,
        is_match,
        doc_length,
        opt_commit,
    );

    if can_hashcahin {
        let nlookup = full_round_cost_model(
            dfa,
            batch_size,
            opt_batching,
            is_match,
            doc_length,
            JCommit::Nlookup,
        );
        if nlookup < cost {
            cost = nlookup;
            opt_commit = JCommit::Nlookup;
        }
    }

    let folding_size: usize = ((cost as f32) / 128.0).log2().ceil() as usize;
    (
        opt_batching,
        opt_commit.clone(),
        batch_size,
        get_folded_cost(cost, doc_length, batch_size),
    )
}

pub fn opt_cost_model_select<'a>(
    dfa: &'a NFA,
    batch_range_lower: usize,
    batch_range_upper: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
    commit: Option<JCommit>,
    batching: Option<JBatching>,
) -> (JBatching, JCommit, usize,usize) {
    let mut opt_batching: JBatching = match batching {
        None => JBatching::NaivePolys,
        Some(b) => b,
    };

    let mut opt_commit: JCommit = match commit {
        None => JCommit::Nlookup,
        Some(c) => c,
    };

    let can_hashcahin: bool = match is_match {
        None => true,
        Some((_, end)) if end == doc_length => true,
        _ => false,
    };

    let mut opt_batch_size: usize = 1;
    let mut cost = full_round_cost_model(
        dfa,
        opt_batch_size,
        opt_batching,
        is_match,
        doc_length,
        opt_commit,
    );
    cost = get_folded_cost(cost, doc_length, 1);

    for n in batch_range_lower..=batch_range_upper {
        let batching_and_cost: (JBatching, JCommit, usize,usize) =
            match (batching.clone(), commit.clone(), can_hashcahin) {
                (None, None, _) => {
                    opt_cost_model_select_with_batch(dfa, 1 << n, is_match, doc_length)
                }
                (_, Some(JCommit::HashChain), false) => {
                    (JBatching::NaivePolys, JCommit::HashChain, 1<<n,cost + 100)
                }
                (None, Some(c), _) => {
                    opt_cost_model_select_with_commit(dfa, 1 << n, is_match, doc_length, c)
                }
                (Some(b), None, _) => {
                    opt_commit_select_with_batch(dfa, 1 << n, is_match, doc_length, b)
                }
                (Some(b), Some(c), _) => {
                    let single_cost =  full_round_cost_model(dfa, 1 << n, b, is_match, doc_length, c);
                    (b, c, 1<<n, get_folded_cost(single_cost, doc_length, 1<<n))
                },
            };
        if batching_and_cost.3 < cost {
            cost = batching_and_cost.3;
            opt_commit = batching_and_cost.1;
            opt_batching = batching_and_cost.0;
            opt_batch_size = 1 << n;
        }
    }
    (opt_batching.clone(), opt_commit.clone(), opt_batch_size,cost)
}
