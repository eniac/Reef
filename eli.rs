        

        // find chars

        let mut alloc_chars = vec![None; DOC LEN];

        for (i, var) in self.r1cs.vars.iter().copied().enumerate() {
            let (name_f, s) = self.generate_variable_info(var);
            let val_f = || {
                Ok({
                    let i_val = &self.values.as_ref().expect("missing values")[i];
                    let ff_val = nova::int_to_ff(i_val.as_pf().into());
                    //debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                    ff_val
                })
            };
 
            let alloc_v = AllocatedNum::alloc(cs.namespace(|| name_f), val_f)?;
            vars.insert(var, alloc_v.get_variable());
 
            if s.starts_with("char_") { // doc.0_n587
                let char_j = Some(alloc_v.clone()); //.get_variable();

                let s_sub: Vec<&str> = s.split("_").collect(); // name = char_i
                let j: usize = s_sub[1].parse().unwrap();

                if j < self.batch_size {
                    alloc_chars[j] = char_j;
                }

            }
        }


        // make hash
        let mut hash_ns = cs.namespace(|| format!("poseidon hash"));
        let acc = &mut hash_ns;
        let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

        sponge.start(
                    IOPattern(vec![SpongeOp::Absorb(DOC LENGTH), SpongeOp::Squeeze(1)]),
                    None,
                    acc,
                );

        let mut elts = vec![];

        for x in alloc_chars {
            elts.push(Elt::Allocated(x.clone()));
        }


        for i in 0..(DOC LENGTH) {
            let unwrap_alloc_char = alloc_chars[i].clone().unwrap();

            let hashed = {

                SpongeAPI::absorb(
                    &mut sponge,
                    DOC LENGTH,
                    &elts,
                    /*&[
                        Elt::Allocated(char_1.clone()), // char_1 type = AllocatedNum
                        Elt::Allocated(char_2.clone()),
                        ...
                    ],*/
                    acc,
                );

                let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

                sponge.finish(acc).unwrap();

                Elt::ensure_allocated(
                    &output[0],
                    &mut hash_ns.namespace(|| "ensure allocated"),
                    true,
                )?
            };


            out = vec![hashed];






