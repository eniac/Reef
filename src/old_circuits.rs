fn lagrange_from_dfa(&self) -> Vec<Integer> {
        let mut evals = vec![];
        for (si, c, so) in self.dfa.deltas() {
            evals.push((
                Integer::from(si * self.dfa.nchars() + self.dfa.ab_to_num(&c.to_string())),
                Integer::from(so),
            ));
        }

        lagrange_field(evals)
    }

// if your mult terms are not yet CirC Terms
fn horners_circuit_const(coeffs: Vec<Integer>, x_lookup: Term) -> Term {
    let mut vars = vec![];
    for c in coeffs {
        vars.push(new_const(c));
    }

    horners_circuit_vars(&vars, x_lookup)
}

// coeffs = [constant, x, x^2 ...]
fn horners_circuit_vars(coeffs: &Vec<Term>, x_lookup: Term) -> Term {
    let num_c = coeffs.len();
    //println!("coeffs = {:#?}", coeffs);

    let mut horners = term(
        Op::PfNaryOp(PfNaryOp::Mul),
        vec![coeffs[num_c - 1].clone(), x_lookup.clone()],
    );
    for i in (1..(num_c - 1)).rev() {
        horners = term(
            Op::PfNaryOp(PfNaryOp::Mul),
            vec![
                x_lookup.clone(),
                term(
                    Op::PfNaryOp(PfNaryOp::Add),
                    vec![horners, coeffs[i].clone()],
                ),
            ],
        );
    }

    // constant
    horners = term(
        Op::PfNaryOp(PfNaryOp::Add),
        vec![horners, coeffs[0].clone()],
    );

    horners
}

fn horners_eval(coeffs: Vec<Integer>, x_lookup: Integer) -> Integer {
    let num_c = coeffs.len();
    let mut horners = coeffs[num_c - 1].clone() * &x_lookup;
    for i in (1..(num_c - 1)).rev() {
        let temp = coeffs[i].clone() + &horners;
        horners = temp * &x_lookup;
        //horners = &x_lookup * (&horners + &coeffs[i]);
    }
    horners += &coeffs[0];
    horners.rem_floor(cfg().field().modulus())
}

fn vanishing(xs: HashSet<usize>) -> Vec<Integer> {
    let mut evals = vec![];
    for xi in xs.into_iter() {
        evals.push((Integer::from(xi), Integer::from(0)));
    }
    // note we don't just want y = 0
    let mut rand = RandState::new();
    evals.push((
        cfg().field().modulus().clone().random_below(&mut rand),
        cfg().field().modulus().clone().random_below(&mut rand),
    )); // todo different? - check not in domain

    lagrange_field(evals)
}

fn lagrange_field(evals: Vec<(Integer, Integer)>) -> Vec<Integer> {
    let num_pts = evals.len();
    //println!("evals = {:#?}", evals);

    let mut coeffs = vec![Integer::from(0); num_pts];
    for i in 0..num_pts {
        // make l_i
        let mut l_i = vec![Integer::from(0); num_pts];
        l_i[0] = denom(i, &evals);

        let mut new_l_i = vec![Integer::from(0); num_pts];
        for k in 0..num_pts {
            if k != i {
                new_l_i = vec![Integer::from(0); num_pts];
                let mut range = (0..k).rev();
                if k < i {
                    range = (0..(k + 1)).rev();
                }
                for j in range {
                    new_l_i[j + 1] += &l_i[j];
                    new_l_i[j] -= &evals[k].0 * &l_i[j];
                    //println!("new_li j, j+1 = {:#?}, {:#?}", new_l_i[j], new_l_i[j + 1]);
                }
                l_i = new_l_i;
            }
        }

        //println!("li = {:#?}", l_i);
        // mult y's
        for k in 0..num_pts {
            coeffs[k] += &evals[i].1 * &l_i[k];
            coeffs[k].rem_floor_assign(cfg().field().modulus());
            //.div_rem_euc(&cfg().field().modulus());
            /*let (_, rem) = coeffs[k]
                .clone()
                .div_rem_euc(cfg().field().modulus().clone());
            coeffs[k] = rem;
            */
        }
    }

    return coeffs;
}

// calculate multilinear extension from evals of univariate
fn mle_from_pts(pts: Vec<Integer>) -> Vec<Integer> {
    let num_pts = pts.len();
    if num_pts == 1 {
        return vec![pts[0].clone()];
    }

    let h = num_pts / 2;
    //println!("num_pts {}, h {}", num_pts, h);

    let mut l = mle_from_pts(pts[..h].to_vec());
    let mut r = mle_from_pts(pts[h..].to_vec());

    for i in 0..r.len() {
        r[i] -= &l[i];
        l.push(r[i].clone().rem_floor(cfg().field().modulus()));
    }

    l
}

// to compute g coeffs each sum check round
// "mle" is coeffs of mle [const, ...]
// "at" should be rev([rand_0, rand_i, ...., -1, {0,1}, {0,1} ...])
// the -1 slot is the "hole" (this will only create a degree 1 univar poly)
// returns [coeff (of "hole"), constant]
// if there is no hole, this will return [0, full result]
fn mle_partial_eval(mle: &Vec<Integer>, at: &Vec<Integer>) -> (Integer, Integer) {
    let base: usize = 2;
    //println!("mle len {:#?} at len {:#?}", mle.len(), at.len());
    assert!(base.pow(at.len() as u32 - 1) <= mle.len());
    assert!(base.pow(at.len() as u32) >= mle.len()); // number of combos = coeffs
                                                     // mle could potentially be computed faster w/better organization .... ugh. we could be optimizing this till we die
                                                     // it's "prover work" tho, so whatever for now

    let mut coeff = Integer::from(0);
    let mut con = Integer::from(0);
    for i in 0..(mle.len()) {
        // for each term
        let mut new_term = mle[i].clone();
        //println!("new term {:#?}", new_term);
        let mut hole_included = false;
        for j in 0..at.len() {
            // for each possible var in this term
            hole_included = hole_included || (((i / base.pow(j as u32)) % 2 == 1) && (at[j] == -1));
            //println!("hole? {:#?}", hole_included);
            if ((i / base.pow(j as u32)) % 2 == 1) && (at[j] != -1) {
                // is this var in this term? AND is this var NOT the hole?
                new_term *= &at[j];
                //println!("new term after mul {:#?}", new_term);
                // note this loop is never triggered for constant :)
            }
        }
        // does this eval belong as a hole coeff? (does this term include the hole?)
        //println!("hole @ end of term? {:#?}", hole_included);
        if hole_included {
            coeff += new_term;
        } else {
            con += new_term;
        }
    }

    (
        coeff.rem_floor(cfg().field().modulus()),
        con.rem_floor(cfg().field().modulus()),
    )
}

// for sum check, computes the sum of many mle univar slices
// takes mle coeffs, and rands = [r_0, r_1,...], leaving off the hole and x_i's
fn mle_sum_evals(mle: &Vec<Integer>, rands: &Vec<Integer>) -> (Integer, Integer) {
    let mut sum_coeff = Integer::from(0);
    let mut sum_con = Integer::from(0);
    let hole = rands.len();
    let total = (mle.len() as f32).log2().ceil() as usize; // total # mle terms

    //println!("#r: {:#?}, #total: {:#?}", hole, total);

    let num_x = total - hole - 1;
    assert!(num_x >= 0, "batch size too small for nlookup");
    let mut opts = vec![];
    for i in 0..num_x {
        opts.push(Integer::from(0));
        opts.push(Integer::from(1));
    }

    for mut combo in opts.into_iter().permutations(num_x).unique() {
        //println!("combo: {:#?}", combo);

        let mut eval_at = rands.clone();
        eval_at.push(Integer::from(-1));
        eval_at.append(&mut combo);
        //println!("eval at: {:#?}", eval_at.clone());
        let (coeff, con) = mle_partial_eval(mle, &eval_at.into_iter().rev().collect());
        //println!("mle partial {:#?}, {:#?}", coeff, con);

        sum_coeff += &coeff;
        sum_con += &con;
    }
    //println!("mle sums {:#?}, {:#?}", sum_coeff, sum_con);
    (
        sum_coeff.rem_floor(cfg().field().modulus()),
        sum_con.rem_floor(cfg().field().modulus()),
    )
}

#[test]
    #[serial]
    fn basic_lg() {
        set_up_cfg("1019".to_owned());
        //set_up_cfg("79".to_owned());

        let points = vec![
            (Integer::from(1), Integer::from(1)),
            (Integer::from(10), Integer::from(10)),
            (Integer::from(3), Integer::from(3)),
            (Integer::from(4), Integer::from(4)),
        ];
        let coeffs = lagrange_field(points);

        let expected = vec![
            Integer::from(0),
            Integer::from(1),
            Integer::from(0),
            Integer::from(0),
        ];

        assert_eq!(coeffs, expected);
    }

#[test]
    #[serial]
    fn lg_1() {
        set_up_cfg("1019".to_owned());

        let points = vec![
            (Integer::from(1), Integer::from(2)),
            (Integer::from(10), Integer::from(3)),
            (Integer::from(3), Integer::from(3)),
            (Integer::from(4), Integer::from(9)),
        ];
        let coeffs = lagrange_field(points);

        let expected = vec![
            Integer::from(124),
            Integer::from(742),
            Integer::from(929),
            Integer::from(245),
        ];

        assert_eq!(coeffs, expected);
    }

#[test]
    fn mle_1() {
        let mut rand = RandState::new();

        let mut points: Vec<(Integer, Integer)> = vec![];
        for x in 0..8 {
            let mut lim = Integer::from(1019);
            lim.random_below_mut(&mut rand);
            points.push((Integer::from(x), lim));
        }
        println!("points: {:#?}", points);
        let uni = points.clone().into_iter().map(|(_, y)| y).collect();

        let coeffs = lagrange_field(points);
        println!("coeffs: {:#?}", coeffs);

        let mle = mle_from_pts(uni);
        println!("mle coeffs: {:#?}", mle);

        for x in vec![Integer::from(0), Integer::from(1)] {
            for y in vec![Integer::from(0), Integer::from(1)] {
                for z in vec![Integer::from(0), Integer::from(1)] {
                    let f: Integer = z.clone() + 2 * y.clone() + 4 * x.clone();

                    let uni_out = horners_eval(coeffs.clone(), f);

                    /*
                    let mle_out = &mle[0]
                        + (&mle[1] * &z)
                        + (&mle[2] * &y)
                        + (&mle[3] * &y * &z)
                        + (&mle[4] * &x)
                        + (mle[5] * &x * &z)
                        + (mle[6] * &x * &y)
                        + (mle[7] * &x * &y * &z);
                    */

                    let vec = vec![z.clone(), y.clone(), x.clone()];
                    let mle_eval = mle_partial_eval(&mle, &vec);

                    assert_eq!(mle_eval.1, uni_out);
                    //assert_eq!(mle_out, mle_eval.1);
                }
            }
        }
    }

#[test]
    fn mle_sums() {
        let mle_T = vec![
            Integer::from(9),
            Integer::from(4),
            Integer::from(5),
            Integer::from(7),
        ];

        // generate polynomial g's for sum check
        let mut sc_rs = vec![];

        // round 1
        let (mut g_coeff, mut g_const) = mle_sum_evals(&mle_T, &sc_rs);
        assert_eq!(g_coeff, Integer::from(17));
        assert_eq!(g_const, Integer::from(22));

        sc_rs.push(Integer::from(10));

        // round 2
        (g_coeff, g_const) = mle_sum_evals(&mle_T, &sc_rs);
        assert_eq!(g_coeff, Integer::from(74));
        assert_eq!(g_const, Integer::from(59));

        sc_rs.push(Integer::from(4));

        // last V check
        (g_coeff, g_const) = mle_partial_eval(&mle_T, &sc_rs.into_iter().rev().collect());
        assert_eq!(g_coeff, Integer::from(0));
        assert_eq!(g_const, Integer::from(355));
    }
