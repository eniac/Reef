use core::{num, panic};
use std::usize::{self};
use std::cmp::max;

use crate::frontend::safa::SAFA;

static POSEIDON_NUM: usize = 292;
static V2: usize = 11376;
static V1: usize = 10347;

pub fn logmn(mn: usize) -> usize {
    match mn {
        1 => 1,
        _ => (mn as f32).log2().ceil() as usize,
    }
}

pub fn get_padding(doc_len: usize, batch_size: usize) -> usize {
    let modlen: usize = doc_len + 1;
    let mut epsilon_to_add = batch_size - (modlen % batch_size);
    if modlen % batch_size == 0 {
        epsilon_to_add = 0;
    }
    epsilon_to_add + 1
}

pub fn lookup_idxs(n_states: usize, batch_size: usize) -> usize {
    let i_leq = logmn(n_states)+1;
    let v_i: usize = 5;
    ((i_leq*3)+v_i)*(batch_size) + (i_leq*3)
}

pub fn nl_nohash<'a>(
    safa: &'a SAFA<char>,
    batch_size: usize,
    table_size: usize,
    hybrid: bool
) -> usize {
    let log_mn: usize = logmn(table_size);
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
    let mut b = batch_size;
    if hybrid {
        b = ((batch_size as f64)/2.0) as usize;
    }
    // cost += 
    lookup_idxs(safa.num_states(), b)
    //;

    // combine qs (for fiat shamir)
    // let num_cqs = ((batch_size * log_mn) as f64 / 254.0).ceil() as usize;

    // cost += num_cqs;

    // cost
}

pub fn nl<'a>(safa: &'a SAFA<char>, batch_size: usize, table_size: usize, hybrid:bool) -> usize{
    let cost_no_hash = nl_nohash(safa, batch_size, table_size, hybrid);
    let cost_hash = nlookup_cost_hash(safa, batch_size, table_size, hybrid);
    //cost_hash+
    cost_no_hash
}

pub fn q_ordering(table_size: usize, batch_size: usize)->usize{
    let logtable = logmn(table_size);
    (logtable+5)*batch_size
}

pub fn nl_doc<'a>(safa: &'a SAFA<char>, batch_size: usize, table_size: usize, hybrid: bool ) -> usize{
    let q_ordering = q_ordering(table_size, batch_size);
    let nl = nl(safa, batch_size, table_size, hybrid);
    q_ordering + nl
}

pub fn cursor_circuit(doc_len: usize,batch_size: usize,max_offset: usize) -> usize {
    let cursor_plus = 1;
    let bitlimit = logmn(max(doc_len,max_offset))+1;
    let ite = 3+3*bitlimit;
    let cur_overflow = bitlimit * (2*batch_size+1);
    let min_offset_leq = bitlimit*3*batch_size;
    let max_offset_geq = bitlimit*2*batch_size;
    let upper_overflow = bitlimit*(batch_size+1);
    cursor_plus+cur_overflow+min_offset_leq+max_offset_geq+upper_overflow+ite
}

pub fn stack_circuit(n_states: usize, doc_len: usize, max_branches: usize, max_stack:usize)->usize{
    let push = 7 + max_branches*(3+logmn(n_states)+max_stack*14);
    // let pop = max_stack*7+logmn(doc_len)+9;
    // let ite = 6; 
    // let stack_ptr = 4; 
    // let not_forall = 14; 
    push
    //+pop+ite+stack_ptr+not_forall
}

pub fn nlookup_cost_hash<'a>(
    safa: &'a SAFA<char>,
    batch_size: usize,
    table_size: usize, 
    hybrid: bool
) -> usize {
    let log_mn: usize = logmn(table_size);
    let num_cqs = ((batch_size * log_mn) as f64 / 254.0).ceil() as usize;
    let mut cost = 0;

    cost += 578;

    //Running claim
    if log_mn + batch_size + num_cqs > 5 {
        let mut num: f32 = (log_mn + num_cqs + batch_size - 5) as f32;
        if hybrid {
            num = num + 1.0;
        }
        let mut n_sponge = ((num / 4.0) as f32).floor() as usize;
        if n_sponge == 0 {
            n_sponge += 1;
        }
        cost += n_sponge * 288;
    }

    //Sum check poseidon hashes
    cost += log_mn * 290;

    cost
}

pub fn full_round_cost_model<'a>(
    safa: &'a SAFA<char>,
    batch_size: usize,
    doc_len: usize,
    hybrid: bool, 
    hybrid_len: Option<usize>,
    max_offset: usize, 
    max_branches: usize, 
    max_stack:usize
) -> usize {
    let total_nl_cost: usize; 
    let dlen_pow2 = doc_len.next_power_of_two();
    let safa_pow2 = safa.num_edges().next_power_of_two();
    if hybrid {
        total_nl_cost = nl_doc(safa, batch_size*2, hybrid_len.unwrap(), hybrid);
    }
    else {
        let nl_cost = nl(safa, batch_size,safa_pow2, false);
        let commit_cost = nl_doc(safa, batch_size, dlen_pow2, hybrid);
        total_nl_cost = nl_cost
        // + commit_cost;
    }
    let cursor_cost = cursor_circuit(dlen_pow2, batch_size, max_offset);
    let stack_cost = stack_circuit(safa.num_states(), dlen_pow2, max_branches, max_stack);
    //total_nl_cost
    //+
    stack_cost
    //+cursor_cost
}

pub fn get_folded_cost(cost: usize, doc_len: usize, batch_size: usize) -> usize {
    if cost == std::usize::MAX {
        return std::usize::MAX;
    }
    let n_foldings = ((doc_len as f32) / (batch_size as f32) as f32).ceil() as usize;
    2*n_foldings*(V1+V2+cost) + 8*(V1+cost)
}

pub fn opt_cost_model_select_with_batch<'a>(
    safa: &'a SAFA<char>,
    batch_size: usize,
    doc_len: usize,
    hybrid: bool, 
    hybrid_len: Option<usize>,
    max_offset: usize, 
    max_branches: usize, 
    max_stack:usize
) -> (usize, usize) {
    let mut cost: usize = full_round_cost_model(
        safa,
        batch_size,
        doc_len,
        hybrid, 
        hybrid_len,
        max_offset,
        max_branches, 
        max_stack,
    );
    (
        batch_size,
        get_folded_cost(cost, doc_len, batch_size),
    )
}

pub fn opt_cost_model_select<'a>(
    safa: &'a SAFA<char>,
    doc_len: usize,
    hybrid: bool, 
    hybrid_len: Option<usize>,
    max_offset: usize, 
    max_branches: usize, 
    max_stack:usize
) -> (usize, usize) {
    let mut opt_batch_size: usize = 1;
    let mut cost = full_round_cost_model(
        safa,
        opt_batch_size,
        doc_len,
        hybrid, 
        hybrid_len,
        max_offset,
        max_branches, 
        max_stack,
    );
    cost = get_folded_cost(cost, doc_len, 1);

    let mut range_list = vec![];

    if doc_len < 100000 {
        range_list = (1..=doc_len).collect();
    } else {
        for n in 1..=logmn(doc_len) {
            range_list.push(1 << n);
        }
    }

    for n in range_list.into_iter() {
        let batching_and_cost: (usize, usize) = opt_cost_model_select_with_batch(
            safa,
            n,
            doc_len,
            hybrid, 
            hybrid_len,
            max_offset,
            max_branches, 
            max_stack,
        );
        println!("Batch size: {:#?}", n);
        println!("{:#?}", batching_and_cost);
        if batching_and_cost.1 < cost {
            cost = batching_and_cost.1;
            opt_batch_size = n.clone();
        }
    }
    (
        opt_batch_size,
        cost,
    )
}
