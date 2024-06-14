#define CHANNEL_SIZE 4
#define TRAFFIC_LIGHTS_NUM 6

// Macros to check if the sensor channels are non-empty
#define s_north_sense_nempty (len(s_north_sense) != 0)
#define e_west_sense_nempty (len(e_west_sense) != 0)
#define e_south_sense_nempty (len(e_south_sense) != 0)
#define s_west_sense_nempty (len(s_west_sense) != 0)
#define w_east_sense_nempty (len(w_east_sense) != 0)
#define p_sense_nempty (len(p_sense) != 0)

bool s_north_buf, e_west_buf, e_south_buf, s_west_buf, w_east_buf;
bool p_buf;

chan s_north_sense = [CHANNEL_SIZE] of {bool};  // South to North (Orange Line)
chan e_west_sense = [CHANNEL_SIZE] of {bool};   // East to West (Black Line)
chan e_south_sense = [CHANNEL_SIZE] of {bool};  // East to South (Purple Line)
chan s_west_sense = [CHANNEL_SIZE] of {bool};   // South to West (Red Line)
chan w_east_sense = [CHANNEL_SIZE] of {bool};   // West to East (Blue Line)
chan p_sense = [CHANNEL_SIZE] of {bool};        // Pedestrian crossing

bool s_north_lock = false, e_west_lock = false, e_south_lock = false;
bool s_west_lock = false, w_east_lock = false, p_lock = false;

bool check_array[TRAFFIC_LIGHTS_NUM];

mtype = { red, green };
mtype s_north_light = red, e_west_light = red, e_south_light = red;
mtype s_west_light = red, w_east_light = red, p_light = red;

// Inline function for checking and resetting the check array
inline check_light(pointer) {
    check_array[pointer] = true;
    bool result = true;
    int i;
    for (i : 0 .. (TRAFFIC_LIGHTS_NUM - 1)) {
        if
            :: check_array[i] == false -> result = false;
            :: else -> skip;
        fi;
    }
    if
        :: result == true ->
            for (i : 0 .. (TRAFFIC_LIGHTS_NUM - 1)) {
                check_array[i] = false;
            }
        :: else -> skip;
    fi;
}

// Process to control the South to North traffic light (Orange Line)
active proctype S_North_con() {
    int process_num = 0;
    do
       :: if
             // If there is a request from the South to North sensor and the light hasn't been checked
             :: len(s_north_sense) > 0 && !check_array[process_num] -> 
                // Ensure East to South or East to West directions are not locked
                (!e_south_lock && !e_west_lock) ->
                {
                    s_north_lock = true;
                    atomic {
                        s_north_light = green;
                        printf("South to North (Orange) light green\n");
                    }
                    s_north_sense?s_north_buf; // Wait for the car to pass
                    s_north_lock = false;
                    atomic {
                        s_north_light = red;
                        printf("South to North (Orange) light red\n");
                    }
                }
            :: else -> skip;
          fi; 
          check_light(process_num); // Update the check array
    od;
}

// Process to generate South to North traffic requests
active proctype S_North_gen() {
    do
         :: atomic {
             s_north_sense!true;
             printf("South to North (Orange) car generated\n");
         }
    od;
}

// Process to control the East to West traffic light (Black Line)
active proctype E_West_con() {
    int process_num = 1;
    do
    :: if
        // If there is a request from the East to West sensor and the light hasn't been checked
        :: len(e_west_sense) > 0 && !check_array[process_num] ->
            // Ensure South to North, South to West, East to South, and Pedestrian directions are not locked
            (!s_north_lock && !s_west_lock && !e_south_lock && !p_lock) ->
            {
                e_west_lock = true;
                atomic {
                    e_west_light = green;
                    printf("East to West (Black) light green\n");
                }
                e_west_sense?e_west_buf; // Wait for the car to pass
                e_west_lock = false;
                atomic {
                    e_west_light = red;
                    printf("East to West (Black) light red\n");
                }
            }
        :: else -> skip;
    fi;
    check_light(process_num); // Update the check array
    od;
}

// Process to generate East to West traffic requests
active proctype E_West_gen() {
    do
         :: atomic {
             e_west_sense!true;
             printf("East to West (Black) car generated\n");
         }
    od;
}

// Process to control the East to South traffic light (Purple Line)
active proctype E_South_con() {
    int process_num = 2;
    do
       :: if
             // If there is a request from the East to South sensor and the light hasn't been checked
             :: len(e_south_sense) > 0 && !check_array[process_num] ->
                // Ensure South to North and South to West directions are not locked
                (!s_north_lock && !s_west_lock && !p_lock) ->
                {
                    e_south_lock = true;
                    atomic {
                        e_south_light = green;
                        printf("East to South (Purple) light green\n");
                    }
                    e_south_sense?e_south_buf; // Wait for the car to pass
                    e_south_lock = false;
                    atomic {
                        e_south_light = red;
                        printf("East to South (Purple) light red\n");
                    }
                }
            :: else -> skip;
          fi; 
          check_light(process_num); // Update the check array
    od;
}

// Process to generate East to South traffic requests
active proctype E_South_gen() {
    do
         :: atomic {
             e_south_sense!true;
             printf("East to South (Purple) car generated\n");
         }
    od;
}

// Process to control the South to West traffic light (Red Line)
active proctype S_West_con() {
    int process_num = 3;
    do
       :: if
             // If there is a request from the South to West sensor and the light hasn't been checked
             :: len(s_west_sense) > 0 && !check_array[process_num] ->
                // Ensure South to North and East to South directions are not locked
                (!s_north_lock && !e_south_lock) ->
                {
                    s_west_lock = true;
                    atomic {
                        s_west_light = green;
                        printf("South to West (Red) light green\n");
                    }
                    s_west_sense?s_west_buf; // Wait for the car to pass
                    s_west_lock = false;
                    atomic {
                        s_west_light = red;
                        printf("South to West (Red) light red\n");
                    }
                }
            :: else -> skip;
          fi; 
          check_light(process_num); // Update the check array
    od;
}

// Process to generate South to West traffic requests
active proctype S_West_gen() {
    do
         :: atomic {
             s_west_sense!true;
             printf("South to West (Red) car generated\n");
         }
    od;
}

// Process to control the West to East traffic light (Blue Line)
active proctype W_East_con() {
    int process_num = 4;
    do
        :: if
            // If there is a request from the West to East sensor and the light hasn't been checked
            :: len(w_east_sense) > 0 && !check_array[process_num] ->
                // Ensure South to North, East to West, and East to South directions are not locked
                (!s_north_lock && !e_west_lock && !p_lock) ->
                {
                    w_east_lock = true;
                    atomic {
                        w_east_light = green;
                        printf("West to East (Blue) light green\n");
                    }
                    w_east_sense?w_east_buf; // Wait for the car to pass
                    w_east_lock = false;
                    atomic {
                        w_east_light = red;
                        printf("West to East (Blue) light red\n");
                    }
                }
            :: else -> skip;
        fi;
        check_light(process_num); // Update the check array
    od;
}

// Process to generate West to East traffic requests
active proctype W_East_gen() {
    do
         :: atomic {
             w_east_sense!true;
             printf("West to East (Blue) car generated\n");
         }
    od;
}

// Process to control the pedestrian crossing
active proctype Pedestrian_con() {
    int process_num = 5;
    do
        :: if
            // If there is a request from the Pedestrian sensor and the light hasn't been checked
            :: len(p_sense) > 0 && !check_array[process_num] ->
                // Ensure East to South and East to West directions are not locked
                (!e_south_lock && !e_west_lock) ->
                {
                    p_lock = true;
                    atomic {
                        p_light = green;
                        printf("Pedestrian light green\n");
                    }
                    p_sense?p_buf; // Wait for the pedestrian to cross
                    p_lock = false;
                    atomic {
                        p_light = red;
                        printf("Pedestrian light red\n");
                    }
                }
            :: else -> skip;
        fi;
        check_light(process_num); // Update the check array
    od;
}

// Process to generate pedestrian requests
active proctype Pedestrian_gen() {
    do
         :: atomic {
             p_sense!true;
             printf("Pedestrian generated\n");
         }
    od;
}

// LTL properties for verification

// safety

// Ensure that not all three traffic lights (South to North, South to West, East to South) are green simultaneously
ltl no_three_lights_green {
    [] !((s_north_light == green) && (s_west_light == green) && (e_south_light == green))
};

// Ensure that not all traffic lights (East to West, South to West, South to North, Pedestrian) are green simultaneously
ltl no_all_lights_green {
    [] !((e_west_light == green) && (s_west_light == green) && (s_north_light == green) && (p_light == green))
};

// Ensure that the East to South and Pedestrian lights are not green simultaneously
ltl no_east_south_and_pedestrian_green {
    [] !((e_south_light == green) && (p_light == green))
};

// liveness

// If there is a continuous request from the South to North sensor, the South to North light will eventually turn green
ltl south_to_north_request_eventually_green {
    (
        ([]<> !((s_north_light == green) && s_north_sense_nempty))
    ) -> (
        ([] ((s_north_sense_nempty && (s_north_light == red)) -> (<> (s_north_light == green))))
    )
};

// If there is a continuous request from the East to West sensor, the East to West light will eventually turn green
ltl east_to_west_request_eventually_green {
    (
        ([]<> !((e_west_light == green) && e_west_sense_nempty))
    ) -> (
        ([] ((e_west_sense_nempty && (e_west_light == red)) -> (<> (e_west_light == green))))
    )
};

// If there is a continuous request from the East to South sensor, the East to South light will eventually turn green
ltl east_to_south_request_eventually_green {
    (
        ([]<> !((e_south_light == green) && e_south_sense_nempty))
    ) -> (
        ([] ((e_south_sense_nempty && (e_south_light == red)) -> (<> (e_south_light == green))))
    )
};

// If there is a continuous request from the South to West sensor, the South to West light will eventually turn green - error
ltl south_to_west_request_eventually_green {
    (
        ([]<> !((s_west_light == green) && s_west_sense_nempty))
    ) -> (
        ([] ((s_west_sense_nempty && (s_west_light == red)) -> (<> (s_west_light == green))))
    )
};

// If there is a continuous request from the West to East sensor, the West to East light will eventually turn green - error
ltl west_to_east_request_eventually_green {
    (
        ([]<> !((w_east_light == green) && w_east_sense_nempty))
    ) -> (
        ([] ((w_east_sense_nempty && (w_east_light == red)) -> (<> (w_east_light == green))))
    )
};

// If there is a continuous request from the Pedestrian sensor, the Pedestrian light will eventually turn green - error
ltl pedestrian_request_eventually_green {
    (
        ([]<> !((p_light == green) && p_sense_nempty))
    ) -> (
        ([] ((p_sense_nempty && (p_light == red)) -> (<> (p_light == green))))
    )
};

// Fairness LTL properties

// Ensure that if there is always a request from the South to North sensor, the South to North traffic light will eventually turn green
ltl fairness_south_to_north {
    [] (s_north_sense_nempty -> <> (s_north_light == green))
}

// Ensure that if there is always a request from the East to West sensor, the East to West traffic light will eventually turn green
ltl fairness_east_to_west {
    [] (e_west_sense_nempty -> <> (e_west_light == green))
}

// Ensure that if there is always a request from the East to South sensor, the East to South traffic light will eventually turn green
ltl fairness_east_to_south {
    [] (e_south_sense_nempty -> <> (e_south_light == green))
}

// Ensure that if there is always a request from the South to West sensor, the South to West traffic light will eventually turn green - error
ltl fairness_south_to_west {
    [] (s_west_sense_nempty -> <> (s_west_light == green))
}

// Ensure that if there is always a request from the West to East sensor, the West to East traffic light will eventually turn green - error
ltl fairness_west_to_east {
    [] (w_east_sense_nempty -> <> (w_east_light == green))
}

// Ensure that if there is always a request from the Pedestrian sensor, the Pedestrian light will eventually turn green - error
ltl fairness_pedestrian {
    [] (p_sense_nempty -> <> (p_light == green))
}



/// from task description:

// Safety: No two traffic lights can show green in intersecting directions:

ltl no_intersecting_lights_green_1 {
    [] !((s_north_light == green) && (s_west_light == green))
}

ltl no_intersecting_lights_green_3 {
    [] !((s_west_light == green) && (e_west_light == green))
}
ltl no_intersecting_lights_green_4 {
    [] !((s_west_light == green) && (w_east_light == green))
}
ltl no_intersecting_lights_green_5 {
    [] !((e_south_light == green) && (w_east_light == green))
}
ltl no_intersecting_lights_green_6 {
    [] !((e_west_light == green) && (w_east_light == green))
}
ltl no_intersecting_lights_green_7 {
    [] !((e_west_light == green) && (p_light == green))
}
ltl no_intersecting_lights_green_8 {
    [] !((e_south_light == green) && (p_light == green))
}
ltl no_intersecting_lights_green_9 {
    [] !((s_west_light == green) && (p_light == green))
}

/// Liveness: Eventually, each traffic light will turn green if there is a continuous request:

ltl south_to_north_liveness {
    [] (s_north_sense_nempty -> <> (s_north_light == green))
}
ltl east_to_west_liveness {
    [] (e_west_sense_nempty -> <> (e_west_light == green))
}
ltl east_to_south_liveness {
    [] (e_south_sense_nempty -> <> (e_south_light == green))
}

// Fairness: No traffic light remains green infinitely often without serving others

ltl south_to_north_fairness {
    [] (<> s_north_sense_nempty -> <> (s_north_light == green))
}
ltl east_to_west_fairness {
    [] (<> e_west_sense_nempty -> <> (e_west_light == green))
}
ltl east_to_south_fairness {
    [] (<> e_south_sense_nempty -> <> (e_south_light == green))
}

