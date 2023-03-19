
use crate::dfa::DFA;

static POSEIDON_NUM: usize = 238; // jess took literal measurement and 238 is the real diff


#[derive(Debug, Clone)]
pub enum JBatching {
    NaivePolys,
    Plookup,
    Nlookup,
}

pub fn naive_cost_model_nohash<'a>(dfa: &'a DFA, batch_size: usize, is_match: bool) -> usize {
    // vanishing poly - m * n multiplications + 2 for lookup
    let mut cost = dfa.nstates() * dfa.nchars() + 2;
    cost *= batch_size;

    // vanishing selection for final check
    // poly of degree (# final states - 1)
    // (alt, # non final states - 1)
    // + 3 for round_num selection + 1 for next_round_num
    if is_match {
        cost += dfa.get_final_states().len() as usize + 3;
    } else {
        cost += dfa.get_non_final_states().len() as usize + 3;
    }

    cost
}

pub fn plookup_cost_model_nohash<'a>(dfa: &'a DFA, batch_size: usize) -> usize {
    let mut cost = 0;
    // 2 prove sequence constructions
    cost = dfa.nstates() * dfa.nchars();
    cost += batch_size;
    cost = cost * 2;

    //Batchsize creating v_i
    cost += 3 * batch_size;

    //Schwarz Zippel evals of sequence
    cost += 2 * ((dfa.nstates() * dfa.nchars()) + batch_size);

    cost
}

pub fn plookup_cost_model_hash<'a>(dfa: &'a DFA, batch_size: usize) -> usize {
    let mut cost: usize = plookup_cost_model_nohash(dfa, batch_size);

    //Randomized difference
    cost += 2 * POSEIDON_NUM;

    //Poseidon hash in Schwarz Zippel
    cost += POSEIDON_NUM;

    cost
}

pub fn nlookup_cost_model_nohash<'a>(dfa: &'a DFA, batch_size: usize) -> usize {
    let mn: usize = dfa.nstates() * dfa.ab.len();
    let log_mn: usize = (mn as f32).log2().ceil() as usize;
    let mut cost: usize = 0;

    //Multiplications
    cost += batch_size + 1;

    //Sum-check additions
    cost += log_mn * 3;

    //eq calc
    cost += (batch_size + 1) * log_mn;

    //horners
    cost += batch_size * 2;

    //v_i creation
    cost += batch_size * 3;

    cost
}

pub fn nlookup_cost_model_hash<'a>(dfa: &'a DFA, batch_size: usize) -> usize {
    let mn: usize = dfa.nstates() * dfa.ab.len();
    let log_mn: usize = (mn as f32).log2().ceil() as usize;
    let mut cost = nlookup_cost_model_nohash(dfa, batch_size);

    //R generation hashes
    cost += POSEIDON_NUM;

    //Sum check poseidon hashes
    cost += log_mn * POSEIDON_NUM;

    cost
}

pub fn full_round_cost_model_nohash<'a>(
    dfa: &'a DFA,
    batch_size: usize,
    lookup_type: JBatching,
    is_match: bool,
) -> usize {
    let mut cost = match lookup_type {
        JBatching::NaivePolys => naive_cost_model_nohash(dfa, batch_size, is_match),
        JBatching::Nlookup => nlookup_cost_model_nohash(dfa, batch_size),
        JBatching::Plookup => plookup_cost_model_nohash(dfa, batch_size),
    };
    cost
}

pub fn full_round_cost_model<'a>(
    dfa: &'a DFA,
    batch_size: usize,
    lookup_type: JBatching,
    is_match: bool,
) -> usize {
    let mut cost = match lookup_type {
        JBatching::NaivePolys => naive_cost_model_nohash(dfa, batch_size, is_match),
        JBatching::Nlookup => nlookup_cost_model_hash(dfa, batch_size),
        JBatching::Plookup => plookup_cost_model_hash(dfa, batch_size),
    };
    cost += POSEIDON_NUM * batch_size;
    cost
}

pub fn opt_cost_model_select_with_batch<'a>(
    dfa: &'a DFA,
    batch_size: usize,
    is_match: bool,
    doc_length: usize,
) -> (JBatching, usize) {
    let mut opt_batching: JBatching = JBatching::NaivePolys;
    let mut cost: usize =
        full_round_cost_model(dfa, batch_size, JBatching::NaivePolys, is_match);

    if full_round_cost_model(dfa, batch_size, JBatching::Nlookup, is_match) < cost {
        cost = full_round_cost_model(dfa, batch_size, JBatching::Nlookup, is_match);
        opt_batching = JBatching::Nlookup;
    }

    if full_round_cost_model(dfa, batch_size, JBatching::Plookup, is_match) < cost {
        cost = full_round_cost_model(dfa, batch_size, JBatching::Plookup, is_match);
        opt_batching = JBatching::Plookup;
    }

    (opt_batching, (cost + 10000)*(2*(doc_length / batch_size)+8))
}
pub fn opt_cost_model_select<'a>(
    dfa: &'a DFA,
    batch_range_lower: usize,
    batch_range_upper: usize,
    is_match: bool,
    doc_length: usize,
) -> JBatching {
    let mut opt_batching: JBatching = JBatching::NaivePolys;
    let mut cost = full_round_cost_model(
        dfa,
        2 << batch_range_lower,
        JBatching::NaivePolys,
        is_match,
    );

    for n in batch_range_lower..batch_range_upper + 1 {
        let batching_and_cost: (JBatching, usize) =
            opt_cost_model_select_with_batch(dfa, 2 << n, is_match, doc_length);
        if batching_and_cost.1 < cost {
            cost = batching_and_cost.1;
            opt_batching = batching_and_cost.0;
        }
    }
    opt_batching
}