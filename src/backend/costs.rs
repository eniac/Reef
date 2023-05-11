use core::panic;

use crate::nfa::NFA;
use clap::ValueEnum;

static POSEIDON_NUM: usize = 292;
static GLUE_NUMBER: usize = 11376 + 10347;
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

pub fn get_padding(doc_len: usize, batch_size: usize, commit: JCommit) -> usize {
    let modlen: usize = match commit {
        JCommit::Nlookup => doc_len + 1,
        _ => doc_len,
    };
    let mut epsilon_to_add = batch_size - (modlen % batch_size);
    if modlen % batch_size == 0 {
        epsilon_to_add = 0;
    }
    epsilon_to_add + 1
}

pub fn accepting_circuit<'a>(nfa: &'a NFA, is_match: Option<(usize, usize)>) -> usize {
    // vanishing selection for final check
    // poly of degree (# final states - 1)
    // (alt, # non final states - 1)
    let cost: usize = 5; //constrain to boolean costs and bool accepting
    let nstate = match is_match {
        None => nfa.get_non_final_states().len() as usize - 1,
        _ => nfa.get_final_states().len() as usize - 1,
    };
    cost + nstate + 2
}

pub fn commit_circuit_nohash(
    doc_len: usize,
    batch_size: usize,
    commit_type: JCommit,
    is_match: Option<(usize, usize)>,
) -> usize {
    match commit_type {
        JCommit::HashChain => match is_match {
            None => batch_size, // i's for hashes: i++ (batch_size),
            // enforce i_0 != 0 bool (2), ite (5) -> on nova level :)
            Some((_, end)) if end >= doc_len => batch_size,
            _ => panic!(
                "Cant do hashchain with substring: doc len {:#?}, substring {:#?}",
                doc_len, is_match
            ),
        },
        JCommit::Nlookup => {
            let match_len = match is_match {
                None => doc_len,
                Some((start, end)) => (end - start) + 1,
            };
            let mn: usize = match_len + get_padding(match_len, batch_size, JCommit::Nlookup);
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
            None => (batch_size + 1) * (POSEIDON_NUM + 3),
            Some((_, end)) if end == doc_len => (batch_size + 1) * POSEIDON_NUM,
            _ => panic!("Cant do hashchain with substring"),
        },
        JCommit::Nlookup => {
            let mod_len = match is_match {
                None => doc_len,
                Some((start, end)) => (end - start) + 1,
            };
            let mn: usize = mod_len + get_padding(mod_len, batch_size, JCommit::Nlookup);
            let log_mn: usize = logmn(mn);
            let mut cost = 578;

            //Running claim
            if log_mn + batch_size > 5 {
                let mut n_sponge = (((log_mn + batch_size - 5) / 4) as f32).ceil() as usize;
                if n_sponge == 0 {
                    n_sponge += 1;
                }
                cost += n_sponge * 288;
            }

            //Sum check poseidon hashes
            cost += log_mn * 290;

            cost
        }
    }
}

pub fn naive_cost_model_nohash<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    // vanishing poly - m * n multiplications + 2 for lookup
    let mut cost = nfa.nedges() - 1;
    cost *= batch_size;

    cost += accepting_circuit(nfa, is_match);

    cost += commit_circuit_nohash(doc_len, batch_size, commit_type, is_match);

    cost
}

pub fn nlookup_cost_model_nohash<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let mn: usize = nfa.nedges();
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

    cost += accepting_circuit(nfa, is_match);

    cost += commit_circuit_nohash(doc_len, batch_size, commit_type, is_match);

    cost
}

pub fn nlookup_cost_model_hash<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let mn: usize = nfa.nedges();
    let log_mn: usize = logmn(mn);
    let mut cost = nlookup_cost_model_nohash(nfa, batch_size, is_match, doc_len, commit_type);

    cost += 578;

    //Running claim
    if log_mn + batch_size > 5 {
        let mut n_sponge = (((log_mn + batch_size - 5) / 4) as f32).ceil() as usize;
        if n_sponge == 0 {
            n_sponge += 1;
        }
        cost += n_sponge * 288;
    }

    //Sum check poseidon hashes
    cost += log_mn * 290;

    cost
}

pub fn full_round_cost_model_nohash<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    lookup_type: JBatching,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let cost = match lookup_type {
        JBatching::NaivePolys => {
            naive_cost_model_nohash(nfa, batch_size, is_match, doc_len, commit_type)
        }
        JBatching::Nlookup => {
            nlookup_cost_model_nohash(nfa, batch_size, is_match, doc_len, commit_type)
        }
    };
    cost
}

pub fn full_round_cost_model<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    lookup_type: JBatching,
    is_match: Option<(usize, usize)>,
    doc_len: usize,
    commit_type: JCommit,
) -> usize {
    let mut cost = match lookup_type {
        JBatching::NaivePolys => {
            naive_cost_model_nohash(nfa, batch_size, is_match, doc_len, commit_type)
        }
        JBatching::Nlookup => {
            nlookup_cost_model_hash(nfa, batch_size, is_match, doc_len, commit_type)
        } //      JBatching::Plookup => plookup_cost_model_hash(nfa, batch_size),
    };

    cost += commit_circuit_hash(doc_len, batch_size, commit_type, is_match);
    cost
}

pub fn get_folded_cost(cost: usize, doc_len: usize, batch_size: usize) -> usize {
    if cost == std::usize::MAX {
        return std::usize::MAX;
    }
    let n_foldings = ((doc_len / batch_size) as f32).ceil() as usize;
    let final_circuit_size = cost + GLUE_NUMBER;
    let cost_folding = 2 * final_circuit_size * n_foldings;
    let cost_snark = (((final_circuit_size) as f32) * 128.0).log2().ceil() as usize;
    let total_cost = cost_folding + cost_snark;
    total_cost
}

pub fn opt_cost_model_select_with_commit<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
    commit: JCommit,
) -> (JBatching, JCommit, usize, usize) {
    let mut opt_batching: JBatching = JBatching::NaivePolys;

    let batch_size_v_match = match is_match {
        None => true,
        Some((start, end)) => ((end - start) + 1) > batch_size,
    };

    let mut mod_len = doc_length;

    let match_len = match is_match {
        None => doc_length,
        Some((start, end)) => end - start + 1,
    };

    let mut cost;
    let nlookup;

    match commit {
        JCommit::HashChain => {
            cost = full_round_cost_model(
                nfa,
                batch_size,
                JBatching::NaivePolys,
                is_match,
                doc_length,
                commit,
            );
            nlookup = full_round_cost_model(
                nfa,
                batch_size,
                JBatching::Nlookup,
                is_match,
                doc_length,
                commit,
            );
        }
        JCommit::Nlookup => {
            if batch_size_v_match {
                cost = full_round_cost_model(
                    nfa,
                    batch_size,
                    JBatching::NaivePolys,
                    is_match,
                    match_len,
                    commit,
                );
                nlookup = full_round_cost_model(
                    nfa,
                    batch_size,
                    JBatching::Nlookup,
                    is_match,
                    match_len,
                    commit,
                );
                mod_len = match_len;
            } else {
                cost = std::usize::MAX;
                nlookup = std::usize::MAX;
            }
        }
    }
    if nlookup < cost {
        cost = nlookup;
        opt_batching = JBatching::Nlookup;
    }
    (
        opt_batching,
        commit.clone(),
        batch_size,
        get_folded_cost(
            cost,
            mod_len + get_padding(mod_len, batch_size, commit),
            batch_size,
        ),
    )
}

pub fn opt_cost_model_select_with_batch<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
) -> (JBatching, JCommit, usize, usize) {
    let mut opt_batching: JBatching = JBatching::NaivePolys;
    let mut opt_commit: JCommit = JCommit::Nlookup;

    let can_hashcahin: bool = match is_match {
        None => true,
        Some((_, end)) if end == doc_length => true,
        _ => false,
    };

    let batch_v_match: bool = match is_match {
        None => true,
        Some((start, end)) => (end - start + 1) >= batch_size,
    };

    let mut mod_len = doc_length;
    let match_len = match is_match {
        None => doc_length,
        Some((start, end)) => end - start + 1,
    };

    let mut cost: usize = std::usize::MAX;

    if batch_v_match {
        let polys_nlookup = full_round_cost_model(
            nfa,
            batch_size,
            JBatching::NaivePolys,
            is_match,
            match_len,
            JCommit::Nlookup,
        );

        if polys_nlookup < cost {
            cost = polys_nlookup;
            opt_batching = JBatching::NaivePolys;
            opt_commit = JCommit::Nlookup;
            mod_len = match_len
        }

        let nlookup_with_nlookup = full_round_cost_model(
            nfa,
            batch_size,
            JBatching::Nlookup,
            is_match,
            match_len,
            JCommit::Nlookup,
        );

        if nlookup_with_nlookup < cost {
            cost = nlookup_with_nlookup;
            opt_batching = JBatching::Nlookup;
            opt_commit = JCommit::Nlookup;
            mod_len = match_len
        }
    }

    if can_hashcahin {
        let nlookup_with_hashchain = full_round_cost_model(
            nfa,
            batch_size,
            JBatching::Nlookup,
            is_match,
            doc_length,
            JCommit::HashChain,
        );
        let naive_with_hashchain = full_round_cost_model(
            nfa,
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
            mod_len = doc_length;
        }
        if naive_with_hashchain < cost {
            cost = naive_with_hashchain;
            opt_batching = JBatching::NaivePolys;
            opt_commit = JCommit::HashChain;
            mod_len = doc_length;
        }
    }

    (
        opt_batching,
        opt_commit.clone(),
        batch_size,
        get_folded_cost(
            cost,
            mod_len + get_padding(mod_len, batch_size, opt_commit),
            batch_size,
        ),
    )
}

pub fn opt_commit_select_with_batch<'a>(
    nfa: &'a NFA,
    batch_size: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
    batching: JBatching,
) -> (JBatching, JCommit, usize, usize) {
    let can_hashcahin: bool = match is_match {
        None => true,
        Some((_, end)) if end == doc_length => true,
        _ => false,
    };

    let batch_v_match: bool = match is_match {
        None => true,
        Some((start, end)) => (end - start + 1) >= batch_size,
    };

    let mut mod_len = doc_length;
    let match_len = match is_match {
        None => doc_length,
        Some((start, end)) => end - start + 1,
    };

    let opt_batching: JBatching = batching;
    let mut cost = std::usize::MAX;
    let mut opt_commit = JCommit::HashChain;

    if can_hashcahin {
        let hashchain = full_round_cost_model(
            nfa,
            batch_size,
            opt_batching,
            is_match,
            doc_length,
            JCommit::HashChain,
        );
        if hashchain < cost {
            cost = hashchain;
            opt_commit = JCommit::HashChain;
        }
    }

    if batch_v_match {
        let nlookup = full_round_cost_model(
            nfa,
            batch_size,
            opt_batching,
            is_match,
            match_len,
            JCommit::Nlookup,
        );
        if nlookup < cost {
            cost = nlookup;
            opt_commit = JCommit::Nlookup;
            mod_len = match_len;
        }
    }

    (
        opt_batching,
        opt_commit.clone(),
        batch_size,
        get_folded_cost(
            cost,
            mod_len + get_padding(mod_len, batch_size, opt_commit),
            batch_size,
        ),
    )
}

pub fn opt_cost_model_select<'a>(
    nfa: &'a NFA,
    batch_range_lower: usize,
    batch_range_upper: usize,
    is_match: Option<(usize, usize)>,
    doc_length: usize,
    commit: Option<JCommit>,
    batching: Option<JBatching>,
) -> (JBatching, JCommit, usize, usize) {
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
        nfa,
        opt_batch_size,
        opt_batching,
        is_match,
        doc_length,
        opt_commit,
    );
    cost = get_folded_cost(
        cost,
        doc_length + get_padding(doc_length, opt_batch_size, opt_commit),
        1,
    );

    let mut range_list = vec![];

    if doc_length < 100000 {
        range_list = (1..=doc_length).collect();
    } else {
        for n in batch_range_lower..=batch_range_upper {
            range_list.push(1 << n);
        }
    }

    for n in range_list.into_iter() {
        let batching_and_cost: (JBatching, JCommit, usize, usize) =
            match (batching.clone(), commit.clone(), can_hashcahin) {
                (None, None, _) => opt_cost_model_select_with_batch(nfa, n, is_match, doc_length),
                (_, Some(JCommit::HashChain), false) => (
                    JBatching::NaivePolys,
                    JCommit::HashChain,
                    n,
                    std::usize::MAX,
                ),
                (None, Some(c), _) => {
                    opt_cost_model_select_with_commit(nfa, n, is_match, doc_length, c)
                }
                (Some(b), None, _) => opt_commit_select_with_batch(nfa, n, is_match, doc_length, b),
                (Some(b), Some(c), _) => {
                    let single_cost = full_round_cost_model(nfa, n, b, is_match, doc_length, c);
                    (
                        b,
                        c,
                        n,
                        get_folded_cost(
                            single_cost,
                            doc_length + get_padding(doc_length, 1 << n, c),
                            1 << n,
                        ),
                    )
                }
            };
        if batching_and_cost.3 < cost {
            cost = batching_and_cost.3;
            opt_commit = batching_and_cost.1;
            opt_batching = batching_and_cost.0;
            opt_batch_size = n.clone();
        }
    }
    (
        opt_batching.clone(),
        opt_commit.clone(),
        opt_batch_size,
        cost,
    )
}
