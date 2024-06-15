import time
import os
import random

traffic_lights = {
    's_north': '🔴',  # South to North (Orange Line)
    'e_west': '🔴',   # East to West (Black Line)
    'e_south': '🔴',  # East to South (Purple Line)
    's_west': '🔴',   # South to West (Red Line)
    'w_east': '🔴',   # West to East (Blue Line)
    'pedestrian': '🔴' # Pedestrian crossing
}

locks = {
    's_north': False,
    'e_west': False,
    'e_south': False,
    's_west': False,
    'w_east': False,
    'pedestrian': False
}

buffers = {
    's_north': [],
    'e_west': [],
    'e_south': [],
    's_west': [],
    'w_east': [],
    'pedestrian': []
}

def clear_console():
    os.system('cls' if os.name == 'nt' else 'clear')

def print_state():
    clear_console()
    print("Traffic Lights State:")
    print(f"South to North (Orange): {traffic_lights['s_north']} | Buffer: {len(buffers['s_north'])} | Lock: {locks['s_north']}")
    print(f"East to West (Black): {traffic_lights['e_west']} | Buffer: {len(buffers['e_west'])} | Lock: {locks['e_west']}")
    print(f"East to South (Purple): {traffic_lights['e_south']} | Buffer: {len(buffers['e_south'])} | Lock: {locks['e_south']}")
    print(f"South to West (Red): {traffic_lights['s_west']} | Buffer: {len(buffers['s_west'])} | Lock: {locks['s_west']}")
    print(f"West to East (Blue): {traffic_lights['w_east']} | Buffer: {len(buffers['w_east'])} | Lock: {locks['w_east']}")
    print(f"Pedestrian: {traffic_lights['pedestrian']} | Buffer: {len(buffers['pedestrian'])} | Lock: {locks['pedestrian']}")
    print("\n")

# some simuate stuff
def simulate_traffic():
    while True:
        traffic_flows = [
            ('s_north', 'e_south', 'e_west'),
            ('e_west', 's_north', 's_west', 'e_south', 'pedestrian'),
            ('e_south', 's_north', 's_west', 'pedestrian'),
            ('s_west', 's_north', 'e_south'),
            ('w_east', 's_north', 'e_west', 'pedestrian'),
            ('pedestrian', 'e_south', 'e_west')
        ]
        
        random.shuffle(traffic_flows)  # random to the resque

        for flow in traffic_flows:
            direction = flow[0]
            dependencies = flow[1:]

            if len(buffers[direction]) > 0 and not any(locks[dep] for dep in dependencies):
                locks[direction] = True
                traffic_lights[direction] = '🟢'
                print_state()
                time.sleep(1)  # green for 1 sec
                traffic_lights[direction] = '🔴'
                locks[direction] = False
                buffers[direction].pop(0)
        
        # Generate requests
        if random.random() < 0.5: buffers['s_north'].append(True)
        if random.random() < 0.5: buffers['e_west'].append(True)
        if random.random() < 0.5: buffers['e_south'].append(True)
        if random.random() < 0.5: buffers['s_west'].append(True)
        if random.random() < 0.5: buffers['w_east'].append(True)
        if random.random() < 0.5: buffers['pedestrian'].append(True)

        print_state()
        time.sleep(1)

simulate_traffic()
