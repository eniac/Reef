How to profile Reef


1) You need to add the following to the Cargo.toml

[profile.release]
debug = true


That will get us the symbols we need. Then you need to recompile (cargo build --release).


2) Before you start Reef, type `sudo perf record -g`. Here's an example.

```
sudo perf record -g ./target/release/reef ...
```

After it completes, you should now see a file called: `perf.data` in the reef folder.
This file has the raw results. The next step is to interpret it. Since we had used "sudo" to collect the data,
perf.data is owned by root. Let's change that.

```
sudo chown sga001 perf.data
```

Now it is owned by my user, so it is easier to open/use, etc.


3) There are many ways to visualize this data. I used flamegraph. To use flamegraph, do the following.


(i) clone this repo https://github.com/brendangregg/FlameGraph
(ii) Type the following:

```
perf script | FlameGraph/stackcollapse-perf.pl | FlameGraph/flamegraph.pl > flame.html
```

Above we assume the folder looks like:

```
reef/perf.data
reef/FlameGraph/
```

and your current directory is reef.

The above command should produce the html document containing the flamegraph.

