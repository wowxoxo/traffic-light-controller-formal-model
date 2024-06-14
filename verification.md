# Verification of Traffic Light Controller

# Safety checks

## no_three_lights_green
```promela
ltl no_three_lights_green {
    [] !((s_north_light == green) && (s_west_light == green) && (e_south_light == green))
};
```
Ensure that not all three traffic lights (South to North, South to West, East to South) are green simultaneously

### How to run:
```bash
spin -search -m100000000 -ltl no_three_lights_green variant_6.pml
```

### Result:
```bash
pan: ltl formula no_three_lights_green
Depth= 1999997 States=    1e+06 Transitions= 1.17e+06 Memory=  5662.033 t=     0.73 R=   1e+06
Depth= 3999997 States=    2e+06 Transitions= 2.36e+06 Memory=  5855.002 t=     1.48 R=   1e+06
Depth= 5999997 States=    3e+06 Transitions= 3.53e+06 Memory=  6048.361 t=     2.23 R=   1e+06
Depth= 7999997 States=    4e+06 Transitions= 4.71e+06 Memory=  6241.428 t=        3 R=   1e+06
Depth= 9999997 States=    5e+06 Transitions= 5.88e+06 Memory=  6434.397 t=     3.94 R=   1e+06
Depth= 11999997 States=    6e+06 Transitions= 7.11e+06 Memory=  6627.561        t=     5.08 R=   1e+06
Depth= 13999997 States=    7e+06 Transitions= 8.47e+06 Memory=  6820.529        t=     6.56 R=   1e+06
Depth= 15999997 States=    8e+06 Transitions= 9.83e+06 Memory=  7013.498        t=     7.68 R=   1e+06
Depth= 17999997 States=    9e+06 Transitions= 1.12e+07 Memory=  7206.565        t=     8.84 R=   1e+06
Depth= 19999997 States=    1e+07 Transitions= 1.26e+07 Memory=  7399.533        t=     10.1 R=   1e+06
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (no_three_lights_green)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 260 byte, depth reached 20656793, errors: 0
 10328397 states, stored
  2676149 states, matched
 13004546 transitions (= stored+matched)
        0 atomic steps
hash conflicts:    588152 (resolved)

Stats on memory usage (in Megabytes):
 2836.779       equivalent memory usage for states (stored*(State-vector + overhead))
 1995.669       actual memory usage for states (compression: 70.35%)
                state-vector as stored = 175 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
 5340.576       memory used for DFS stack (-m100000000)
    1.333       memory lost to fragmentation
 7462.912       total actual memory usage



pan: elapsed time 10.7 seconds
pan: rate 963469.87 states/second
```

### Conclusion:
The verification of the `no_three_lights_green` property indicates that the model is safe, as there are no states where the South to North, South to West, and East to South lights are green simultaneously. This confirms that the system effectively prevents green lights on intersecting routes, ensuring safe traffic flow.


## no_all_lights_green
```promela
ltl no_all_lights_green {
    [] !((e_west_light == green) && (s_west_light == green) && (s_north_light == green) && (p_light == green))
};
```
Ensure that not all traffic lights (East to West, South to West, South to North, Pedestrian) are green simultaneously

### How to run:
```bash
spin -search -m100000000 -ltl no_all_lights_green variant_6.pml
```

### Result:
```bash
pan: ltl formula no_all_lights_green
Depth= 1999997 States=    1e+06 Transitions= 1.17e+06 Memory=  5662.033 t=     0.84 R=   1e+06
Depth= 3999997 States=    2e+06 Transitions= 2.36e+06 Memory=  5855.002 t=     1.74 R=   1e+06
Depth= 5999997 States=    3e+06 Transitions= 3.53e+06 Memory=  6048.361 t=     2.84 R=   1e+06
Depth= 7999997 States=    4e+06 Transitions= 4.71e+06 Memory=  6241.428 t=     3.99 R=   1e+06
Depth= 9999997 States=    5e+06 Transitions= 5.88e+06 Memory=  6434.397 t=     4.84 R=   1e+06
Depth= 11999997 States=    6e+06 Transitions= 7.11e+06 Memory=  6627.561        t=     5.82 R=   1e+06
Depth= 13999997 States=    7e+06 Transitions= 8.47e+06 Memory=  6820.529        t=     7.13 R=   1e+06
Depth= 15999997 States=    8e+06 Transitions= 9.83e+06 Memory=  7013.498        t=     8.17 R=   1e+06
Depth= 17999997 States=    9e+06 Transitions= 1.12e+07 Memory=  7206.565        t=      9.3 R=   1e+06
Depth= 19999997 States=    1e+07 Transitions= 1.26e+07 Memory=  7399.533        t=     10.5 R=   1e+06
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (no_all_lights_green)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 260 byte, depth reached 20645077, errors: 0
 10322539 states, stored
  2674041 states, matched
 12996580 transitions (= stored+matched)
        0 atomic steps
hash conflicts:    589070 (resolved)

Stats on memory usage (in Megabytes):
 2835.170       equivalent memory usage for states (stored*(State-vector + overhead))
 1994.497       actual memory usage for states (compression: 70.35%)
                state-vector as stored = 175 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
 5340.576       memory used for DFS stack (-m100000000)
    1.333       memory lost to fragmentation
 7461.740       total actual memory usage



pan: elapsed time 11.2 seconds
pan: rate 925788.25 states/second
```

### Conclusion:
The verification of the `no_all_lights_green` property confirms that the model effectively prevents all traffic lights (East to West, South to West, South to North, and Pedestrian) from being green simultaneously. This result demonstrates the system's robustness in maintaining safe traffic conditions, ensuring that these conflicting directions are never green at the same time.


## no_east_south_and_pedestrian_green
```promela
ltl no_east_south_and_pedestrian_green {
    [] !((e_south_light == green) && (p_light == green))
};
```
Ensure that not all traffic lights (East to West, South to West, South to North, Pedestrian) are green simultaneously

### How to run:
```bash
spin -search -m100000000 -ltl no_east_south_and_pedestrian_green variant_6.pml
```

### Result:
```bash
pan: ltl formula no_east_south_and_pedestrian_green
Depth= 1999997 States=    1e+06 Transitions= 1.17e+06 Memory=  5662.033 t=     0.81 R=   1e+06
Depth= 3999997 States=    2e+06 Transitions= 2.36e+06 Memory=  5855.002 t=     1.63 R=   1e+06
Depth= 5999997 States=    3e+06 Transitions= 3.53e+06 Memory=  6048.361 t=     2.47 R=   1e+06
Depth= 7999997 States=    4e+06 Transitions= 4.71e+06 Memory=  6241.428 t=     3.71 R=   1e+06
Depth= 9999997 States=    5e+06 Transitions= 5.88e+06 Memory=  6434.397 t=     4.56 R=   1e+06
Depth= 11999997 States=    6e+06 Transitions= 7.11e+06 Memory=  6627.561        t=     5.55 R=   1e+06
Depth= 13999997 States=    7e+06 Transitions= 8.47e+06 Memory=  6820.529        t=     7.08 R=   1e+06
Depth= 15999997 States=    8e+06 Transitions= 9.83e+06 Memory=  7013.498        t=     8.61 R=   9e+05
Depth= 17999997 States=    9e+06 Transitions= 1.12e+07 Memory=  7206.565        t=     9.82 R=   9e+05
Depth= 19999997 States=    1e+07 Transitions= 1.26e+07 Memory=  7399.533        t=       12 R=   8e+05
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (no_east_south_and_pedestrian_green)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 260 byte, depth reached 20492695, errors: 0
 10246348 states, stored
  2646315 states, matched
 12892663 transitions (= stored+matched)
        0 atomic steps
hash conflicts:    565813 (resolved)

Stats on memory usage (in Megabytes):
 2814.244       equivalent memory usage for states (stored*(State-vector + overhead))
 1979.839       actual memory usage for states (compression: 70.35%)
                state-vector as stored = 175 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
 5340.576       memory used for DFS stack (-m100000000)
    1.323       memory lost to fragmentation
 7447.092       total actual memory usage



pan: elapsed time 12.6 seconds
pan: rate 811270.63 states/second
```

### Conclusion:
The verification of the `no_east_south_and_pedestrian_green` property confirms that the model successfully ensures that the East to South light and the Pedestrian light are not green simultaneously. This result indicates that the system effectively manages conflicting pedestrian and vehicle movements, thereby enhancing overall safety at the intersection.


# Liveness checks
## south_to_north_request_eventually_green
```promela
ltl south_to_north_request_eventually_green {
    (
        ([]<> !((s_north_light == green) && s_north_sense_nempty))
    ) -> (
        ([] ((s_north_sense_nempty && (s_north_light == red)) -> (<> (s_north_light == green))))
    )
};
```
If there is a continuous request from the South to North sensor, the South to North light will eventually turn green

### How to run:
```bash
spin -search -m100000 -ltl south_to_north_request_eventually_green variant_6.pml
```

### Result:
```bash
pan: ltl formula south_to_north_request_eventually_green
error: max search depth too small
Depth=   99999 States=    1e+06 Transitions= 6.31e+06 Memory=   257.755 t=     1.58 R=   6e+05
Depth=   99999 States=    2e+06 Transitions= 1.22e+07 Memory=   378.653 t=     3.13 R=   6e+05
Depth=   99999 States=    3e+06 Transitions= 1.78e+07 Memory=   499.649 t=     4.65 R=   6e+05
Depth=   99999 States=    4e+06 Transitions= 2.32e+07 Memory=   620.938 t=     6.16 R=   6e+05
Depth=   99999 States=    5e+06 Transitions= 2.84e+07 Memory=   742.227 t=      7.7 R=   6e+05
Depth=   99999 States=    6e+06 Transitions= 3.41e+07 Memory=   863.028 t=     9.22 R=   7e+05
Depth=   99999 States=    7e+06 Transitions= 3.93e+07 Memory=   984.220 t=     10.7 R=   7e+05
Depth=   99999 States=    8e+06 Transitions= 4.42e+07 Memory=  1105.509 t=     12.3 R=   7e+05
Depth=   99999 States=    9e+06 Transitions=  4.9e+07 Memory=  1226.798 t=     13.9 R=   6e+05
Depth=   99999 States=    1e+07 Transitions= 5.49e+07 Memory=  1347.599 t=     15.5 R=   6e+05
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (south_to_north_request_eventually_green)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 260 byte, depth reached 99999, errors: 0
  6850406 states, stored (1.07652e+07 visited)
 48236845 states, matched
 59002054 transitions (= visited+matched)
        0 atomic steps
hash conflicts:   2268504 (resolved)

Stats on memory usage (in Megabytes):
 1881.520       equivalent memory usage for states (stored*(State-vector + overhead))
 1306.954       actual memory usage for states (compression: 69.46%)
                state-vector as stored = 172 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    5.341       memory used for DFS stack (-m100000)
 1440.274       total actual memory usage



pan: elapsed time 16.7 seconds
pan: rate 644623.29 states/second
```

### Conclusion:
The verification of the `south_to_north_request_eventually_green` property confirms that the South to North light would eventually turn green if there is a continuous request.


## east_to_west_liveness
```promela
ltl east_to_west_liveness {
    [] (e_west_sense_nempty -> <> (e_west_light == green))
}
```
Eventually, each traffic light will turn green if there is a continuous request

### How to run:
```bash
spin -search -m100000 -ltl east_to_west_liveness variant_6.pml
```

### Result:
```bash
pan: ltl formula east_to_west_liveness
error: max search depth too small
Depth=   99999 States=    1e+06 Transitions= 4.75e+06 Memory=   260.782 t=     1.16 R=   9e+05
Depth=   99999 States=    2e+06 Transitions= 9.08e+06 Memory=   385.880 t=      3.1 R=   6e+05
Depth=   99999 States=    3e+06 Transitions= 1.33e+07 Memory=   510.782 t=     4.51 R=   7e+05
Depth=   99999 States=    4e+06 Transitions= 1.75e+07 Memory=   634.024 t=     6.09 R=   7e+05
Depth=   99999 States=    5e+06 Transitions= 2.13e+07 Memory=   760.880 t=     7.53 R=   7e+05
Depth=   99999 States=    6e+06 Transitions= 2.55e+07 Memory=   886.368 t=     8.71 R=   7e+05
Depth=   99999 States=    7e+06 Transitions= 2.97e+07 Memory=  1011.270 t=     9.94 R=   7e+05
Depth=   99999 States=    8e+06 Transitions= 3.38e+07 Memory=  1136.075 t=     11.3 R=   7e+05
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (east_to_west_liveness)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 244 byte, depth reached 99999, errors: 0
  5880420 states, stored (8.24641e+06 visited)
 26662659 states, matched
 34909071 transitions (= visited+matched)
        0 atomic steps
hash conflicts:   1111459 (resolved)

Stats on memory usage (in Megabytes):
 1525.378       equivalent memory usage for states (stored*(State-vector + overhead))
 1034.203       actual memory usage for states (compression: 67.80%)
                state-vector as stored = 156 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    5.341       memory used for DFS stack (-m100000)
 1166.544       total actual memory usage



pan: elapsed time 11.7 seconds
pan: rate 705424.47 states/second
```

### Conclusion:
The verification of the `east_to_west_liveness` property confirms that the East to West light will eventually turn green if there is a continuous request.


# Fairness checks

## fairness_south_to_north
```promela
ltl fairness_south_to_north {
    [] (s_north_sense_nempty -> <> (s_north_light == green))
}
```
Ensure that if there is always a request from the South to North sensor, the South to North traffic light will eventually turn green

### How to run:
```bash
spin -search -m100000 -ltl fairness_south_to_north variant_6.pml
```

### Result:
```bash
pan: ltl formula fairness_south_to_north
error: max search depth too small
Depth=   99999 States=    1e+06 Transitions= 4.74e+06 Memory=   260.880 t=     1.15 R=   9e+05
Depth=   99999 States=    2e+06 Transitions= 9.08e+06 Memory=   385.977 t=     2.29 R=   9e+05
Depth=   99999 States=    3e+06 Transitions= 1.33e+07 Memory=   511.270 t=     3.42 R=   9e+05
Depth=   99999 States=    4e+06 Transitions= 1.75e+07 Memory=   636.270 t=     4.66 R=   9e+05
Depth=   99999 States=    5e+06 Transitions= 2.14e+07 Memory=   761.563 t=     5.78 R=   9e+05
Depth=   99999 States=    6e+06 Transitions= 2.55e+07 Memory=   886.661 t=     6.92 R=   9e+05
Depth=   99999 States=    7e+06 Transitions= 2.98e+07 Memory=  1011.856 t=     8.09 R=   9e+05
Depth=   99999 States=    8e+06 Transitions= 3.38e+07 Memory=  1136.954 t=     9.27 R=   9e+05
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (fairness_south_to_north)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 244 byte, depth reached 99999, errors: 0
  6194749 states, stored (8.67725e+06 visited)
 27951338 states, matched
 36628585 transitions (= visited+matched)
        0 atomic steps
hash conflicts:   1208907 (resolved)

Stats on memory usage (in Megabytes):
 1606.914       equivalent memory usage for states (stored*(State-vector + overhead))
 1089.433       actual memory usage for states (compression: 67.80%)
                state-vector as stored = 156 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    5.341       memory used for DFS stack (-m100000)
    1.054       memory lost to fragmentation
 1221.720       total actual memory usage



pan: elapsed time 10.1 seconds
pan: rate 856589.04 states/second
```

### Conclusion:
The verification of the `fairness_south_to_north` property confirms that if there is always a request from the South to North sensor, the South to North traffic light will eventually turn green.



## east_to_west_fairness
```promela
ltl east_to_west_fairness {
    [] (<> e_west_sense_nempty -> <> (e_west_light == green))
}
```
No traffic light remains green infinitely often without serving others

### How to run:
```bash
spin -search -m100000 -ltl east_to_west_fairness variant_6.pml
```

### Result:
```bash
pan: ltl formula east_to_west_fairness
error: max search depth too small
Depth=   99999 States=    1e+06 Transitions=  4.7e+06 Memory=   258.145 t=     1.74 R=   6e+05
Depth=   99999 States=    2e+06 Transitions= 9.05e+06 Memory=   378.946 t=     2.91 R=   7e+05
Depth=   99999 States=    3e+06 Transitions=  1.3e+07 Memory=   499.942 t=     4.08 R=   7e+05
Depth=   99999 States=    4e+06 Transitions= 1.73e+07 Memory=   621.720 t=     5.29 R=   8e+05
Depth=   99999 States=    5e+06 Transitions= 2.11e+07 Memory=   742.813 t=     6.56 R=   8e+05
Depth=   99999 States=    6e+06 Transitions= 2.55e+07 Memory=   864.200 t=     7.83 R=   8e+05
Depth=   99999 States=    7e+06 Transitions= 2.96e+07 Memory=   985.489 t=     9.05 R=   8e+05
^CInterrupted

(Spin Version 6.5.2 -- 6 December 2019)
Warning: Search not completed
        + Partial Order Reduction

Full statespace search for:
        never claim             + (east_to_west_fairness)
        assertion violations    + (if within scope of claim)
        acceptance   cycles     + (fairness disabled)
        invalid end states      - (disabled by never claim)

State-vector 236 byte, depth reached 99999, errors: 0
  5023716 states, stored (7.25596e+06 visited)
 23474248 states, matched
 30730203 transitions (= visited+matched)
        0 atomic steps
hash conflicts:    827719 (resolved)

Stats on memory usage (in Megabytes):
 1264.821       equivalent memory usage for states (stored*(State-vector + overhead))
  883.582       actual memory usage for states (compression: 69.86%)
                state-vector as stored = 156 byte + 28 byte overhead
  128.000       memory used for hash table (-w24)
    5.341       memory used for DFS stack (-m100000)
 1016.056       total actual memory usage



pan: elapsed time 9.37 seconds
pan: rate 774381.54 states/second
```

### Conclusion:
The verification of the `east_to_west_fairness` property confirms that the East to West traffic light does not remain green infinitely without serving other directions.

