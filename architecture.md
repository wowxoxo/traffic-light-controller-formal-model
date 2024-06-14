# Solution Architecture
## Constants and Macros
### CHANNEL_SIZE
```promela
#define CHANNEL_SIZE 4
```

Defines the size of each channel, indicating the maximum number of messages (requests) that the channel can hold at a time.

### TRAFFIC_LIGHTS_NUM
```promela
#define TRAFFIC_LIGHTS_NUM 6
```
Defines the total number of traffic lights in the system, including the pedestrian light.

### Sensor Non-Empty Macros
```promela
#define s_north_sense_nempty (len(s_north_sense) != 0)
#define e_west_sense_nempty (len(e_west_sense) != 0)
#define e_south_sense_nempty (len(e_south_sense) != 0)
#define s_west_sense_nempty (len(s_west_sense) != 0)
#define w_east_sense_nempty (len(w_east_sense) != 0)
#define p_sense_nempty (len(p_sense) != 0)
```

These macros check if the corresponding sensor channels are non-empty, indicating that there are pending requests.

## 2. Buffers and Channels
### Buffers
```promela
#define s_north_sense_nempty (len(s_north_sense) != 0)
#define e_west_sense_nempty (len(e_west_sense) != 0)
#define e_south_sense_nempty (len(e_south_sense) != 0)
#define s_west_sense_nempty (len(s_west_sense) != 0)
#define w_east_sense_nempty (len(w_east_sense) != 0)
#define p_sense_nempty (len(p_sense) != 0)
```

Buffers are used to temporarily hold the sensor signals.

### Channels
```promela
chan s_north_sense = [CHANNEL_SIZE] of {bool};  // South to North (Orange Line)
chan e_west_sense = [CHANNEL_SIZE] of {bool};   // East to West (Black Line)
chan e_south_sense = [CHANNEL_SIZE] of {bool};  // East to South (Purple Line)
chan s_west_sense = [CHANNEL_SIZE] of {bool};   // South to West (Red Line)
chan w_east_sense = [CHANNEL_SIZE] of {bool};   // West to East (Blue Line)
chan p_sense = [CHANNEL_SIZE] of {bool};        // Pedestrian crossing
```

Channels are used for communication between the sensor generators and the traffic light controllers. Each channel represents a specific traffic direction or pedestrian crossing.

## 3. Locks
```promela
bool s_north_lock = false, e_west_lock = false, e_south_lock = false;
bool s_west_lock = false, w_east_lock = false, p_lock = false;
```

Locks ensure that conflicting directions do not have green lights simultaneously, preventing potential traffic conflicts.

## 4. Traffic Light States
```promela
mtype = { red, green };
mtype s_north_light = red, e_west_light = red, e_south_light = red;
mtype s_west_light = red, w_east_light = red, p_light = red;
```

These variables represent the current state (red or green) of each traffic light.

## 5. Check Array
```promela
bool check_array[TRAFFIC_LIGHTS_NUM];
```

The check array is used to ensure fairness by tracking which lights have been checked and ensuring all lights get their turn to be green.

## 6. Inline Functions
### Check Light
```promela
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
```
The `check_light` function updates the check array and ensures that all lights are fairly checked.

## 7. Processes
### Conceptual Flow
The solution consists of two main pieces for each traffic flow and the pedestrian crossing: the **Controller** and the **Generator**.

#### Controller
The controller process manages the state of the traffic light for a specific direction. It checks if there are any pending requests and whether it can safely turn the light green without causing conflicts. If these conditions are met, it turns the light green, processes the request, and then turns the light red again.

#### Generator
The generator process simulates traffic requests for a specific direction. It continuously generates requests that are sent to the corresponding sensor channel.

### South to North (Orange Line)
#### Controller
```promela
active proctype S_North_con() {
    int process_num = 0;
    do
       :: if
             :: len(s_north_sense) > 0 && !check_array[process_num] -> 
                (!e_south_lock && !e_west_lock) ->
                {
                    s_north_lock = true;
                    atomic {
                        s_north_light = green;
                        printf("South to North (Orange) light green\n");
                    }
                    s_north_sense?s_north_buf; 
                    s_north_lock = false;
                    atomic {
                        s_north_light = red;
                        printf("South to North (Orange) light red\n");
                    }
                }
            :: else -> skip;
          fi; 
          check_light(process_num);
    od;
}
```

#### Generator
```promela
active proctype S_North_gen() {
    do
         :: atomic {
             s_north_sense!true;
             printf("South to North (Orange) car generated\n");
         }
    od;
}
```


### East to West (Black Line)
#### Controller
```promela
active proctype E_West_con() {
    int process_num = 1;
    do
    :: if
        :: len(e_west_sense) > 0 && !check_array[process_num] ->
            (!s_north_lock && !s_west_lock && !e_south_lock && !p_lock) ->
            {
                e_west_lock = true;
                atomic {
                    e_west_light = green;
                    printf("East to West (Black) light green\n");
                }
                e_west_sense?e_west_buf;
                e_west_lock = false;
                atomic {
                    e_west_light = red;
                    printf("East to West (Black) light red\n");
                }
            }
        :: else -> skip;
    fi;
    check_light(process_num);
    od;
}
```

#### Generator
```promela
active proctype E_West_gen() {
    do
         :: atomic {
             e_west_sense!true;
             printf("East to West (Black) car generated\n");
         }
    od;
}
```


### East to South (Purple Line)
#### Controller
```promela
active proctype E_South_con() {
    int process_num = 2;
    do
       :: if
             :: len(e_south_sense) > 0 && !check_array[process_num] ->
                (!s_north_lock && !s_west_lock && !p_lock) ->
                {
                    e_south_lock = true;
                    atomic {
                        e_south_light = green;
                        printf("East to South (Purple) light green\n");
                    }
                    e_south_sense?e_south_buf;
                    e_south_lock = false;
                    atomic {
                        e_south_light = red;
                        printf("East to South (Purple) light red\n");
                    }
                }
            :: else -> skip;
          fi; 
          check_light(process_num);
    od;
}
```

#### Generator
```promela
active proctype E_South_gen() {
    do
         :: atomic {
             e_south_sense!true;
             printf("East to South (Purple) car generated\n");
         }
    od;
}
```


### South to West (Red Line)
#### Controller
```promela
active proctype S_West_con() {
    int process_num = 3;
    do
       :: if
             :: len(s_west_sense) > 0 && !check_array[process_num] ->
                (!s_north_lock && !e_south_lock) ->
                {
                    s_west_lock = true;
                    atomic {
                        s_west_light = green;
                        printf("South to West (Red) light green\n");
                    }
                    s_west_sense?s_west_buf;
                    s_west_lock = false;
                    atomic {
                        s_west_light = red;
                        printf("South to West (Red) light red\n");
                    }
                }
            :: else -> skip;
          fi; 
          check_light(process_num);
    od;
}
```

#### Generator
```promela
active proctype S_West_gen() {
    do
         :: atomic {
             s_west_sense!true;
             printf("South to West (Red) car generated\n");
         }
    od;
}
```


### West to East (Blue Line)
#### Controller
```promela
active proctype W_East_con() {
    int process_num = 4;
    do
        :: if
            :: len(w_east_sense) > 0 && !check_array[process_num] ->
                (!s_north_lock && !e_west_lock && !p_lock) ->
                {
                    w_east_lock = true;
                    atomic {
                        w_east_light = green;
                        printf("West to East (Blue) light green\n");
                    }
                    w_east_sense?w_east_buf;
                    w_east_lock = false;
                    atomic {
                        w_east_light = red;
                        printf("West to East (Blue) light red\n");
                    }
                }
            :: else -> skip;
        fi;
        check_light(process_num);
    od;
}
```

#### Generator
```promela
active proctype W_East_gen() {
    do
         :: atomic {
             w_east_sense!true;
             printf("West to East (Blue) car generated\n");
         }
    od;
}
```


### Pedestrian Crossing
#### Controller
```promela
active proctype Pedestrian_con() {
    int process_num = 5;
    do
        :: if
            :: len(p_sense) > 0 && !check_array[process_num] ->
                (!e_south_lock && !e_west_lock) ->
                {
                    p_lock = true;
                    atomic {
                        p_light = green;
                        printf("Pedestrian light green\n");
                    }
                    p_sense?p_buf;
                    p_lock = false;
                    atomic {
                        p_light = red;
                        printf("Pedestrian light red\n");
                    }
                }
            :: else -> skip;
        fi;
        check_light(process_num);
    od;
}
```

#### Generator
```promela
active proctype Pedestrian_gen() {
    do
         :: atomic {
             p_sense!true;
             printf("Pedestrian generated\n");
         }
    od;
}
```

## Summary
This architecture ensures that all directions and the pedestrian crossing are managed fairly and safely, with proper synchronization and communication between the processes. The use of channels and locks prevents traffic conflicts, while the check array ensures fairness in the traffic light changes.