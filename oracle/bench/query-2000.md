# Query benchmarks (report-only, D14)

Fixture: 2000 nodes (about 22000 statements); 20 calls per round, median of 5 rounds; times per call in microseconds, driver protocol included.

| Workload | Rust µs | Lean µs | Lean/Rust | Equal |
|---|---|---|---|---|
| point lookup | 65 | 101 | 1.550000 | yes |
| 2-hop lookup | 120 | 300 | 2.500000 | yes |
| acyclic BGP | 6315 | 50932 | 8.060000 | yes |
| rare join | 120 | 221 | 1.830000 | yes |
| path REACH knows{1,3} | 566 | 1298 | 2.290000 | yes |
| path TRAIL knows+ (2 hops) | 530 | 680 | 1.280000 | yes |
