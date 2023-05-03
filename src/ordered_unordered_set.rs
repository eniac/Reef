use reef::Regex;

struct OrderedUnorderedSet<T> {
    ordered: Vec<T>,
    unordered: Vec<T>
}

impl<T> OrderedUnorderedSet<T> {
    fn new() -> Self {
        Self {
            ordered: Vec::new(),
            unordered: Vec::new()
        }
    }

    fn push_ordered(&mut self, t: T) {
        self.ordered.push(t)
    }

    fn push_unordered(&mut self, t: T) {
        self.unordered.push(t)
    }

    fn map<B, F>(self, f: F) -> OrderedUnorderedSet<B>
        where F: Fn(T) -> B {
        OrderedUnorderedSet {
            ordered: self.ordered.into_iter().map(&f).collect(),
            unordered: self.unordered.into_iter().map(&f).collect()
        }
    }
}

impl OrderedUnorderedSet<Regex> {
    fn from_str(rstr: &str) -> Self {
        let mut c = OrderedUnorderedSet::new();
        let mut level = 0;
        let mut j = 0;

        let r = &rstr[..];
        for i in 0..r.len() - 2 {
            if &r[i..i+1] == "(" {
                level += 1;
            } else if &r[i..i+1] == ")" {
                level -= 1;
            } else if &r[i..i+2] == "&&" && level == 0 {
                c.push_unordered(&r[j..i]);
                j = i + 2;
            } else if &r[i..i+2] == ".*" && level == 0 {
                c.push_ordered(&r[j..i]);
                j = i + 2;
            }
        }
        if j != r.len() {
            c.push_ordered(&r[j..r.len()]);
        }

        c.map(|s| Regex::new(s))
    }
}

impl FromStr for OrderedUnorderedSet<Regex> {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut c = OrderedUnorderedSet::new();
        let mut level = 0;
        let mut j = 0;

        let r = &rstr[..];
        for i in 0..r.len() - 2 {
            if &r[i..i+1] == "(" {
                level += 1;
            } else if &r[i..i+1] == ")" {
                level -= 1;
            } else if &r[i..i+2] == "&&" && level == 0 {
                c.push_unordered(&r[j..i]);
                j = i + 2;
            } else if &r[i..i+2] == ".*" && level == 0 {
                c.push_ordered(&r[j..i]);
                j = i + 2;
            }
        }
        if j != r.len() {
            c.push_ordered(&r[j..r.len()]);
        }

        c.map(|s| Regex::from_str(s)?)
    }
}


