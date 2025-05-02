# `sp_pifo.py` Documentation

## Overview
The `sp_pifo.py` script implements a **Strict Priority Push-In First-Out (SP-PIFO)** queueing mechanism. This is a scheduling algorithm designed for packet processing in networking systems. The script simulates how packets are enqueued and dequeued based on their priority and arrival order.

![Alt text here](sp_pifo.svg)

## Features
- **Priority-based Scheduling**: Packets are prioritized based on strict priority levels.
- **Push-In First-Out (PIFO)**: Ensures that higher-priority packets can preempt lower-priority ones in the queue.
- **Customizable Parameters**: Allows configuration of packet attributes like priority and arrival time.
- **Simulation and Debugging**: Provides detailed logs for understanding the queue's behavior.

## Key Components

### 1. **Packet Class**
Represents a network packet with the following attributes:
- `priority`: Integer representing the packet's priority (lower value = higher priority).
- `arrival_time`: Timestamp indicating when the packet arrived.
- `data`: Optional payload or metadata associated with the packet.

### 2. **SPPIFOQueue Class**
Implements the SP-PIFO queue with the following methods:
- `enqueue(packet)`: Adds a packet to the queue based on its priority and arrival time.
- `dequeue()`: Removes and returns the highest-priority packet from the queue.
- `peek()`: Returns the highest-priority packet without removing it.
- `is_empty()`: Checks if the queue is empty.
- `size()`: Returns the current number of packets in the queue.

### 3. **Utility Functions**
- `generate_packets(n)`: Creates `n` packets with random priorities and arrival times for testing.
- `simulate_queue_behavior()`: Demonstrates the enqueue and dequeue operations with sample packets.

## Usage

### Prerequisites
Ensure you have Python 3.x installed on your system.

### Running the Script
1. Clone the repository:
    ```bash
    git clone https://github.com/your-repo/sp-pifo.git
    cd sp-pifo
    ```
2. Execute the script:
    ```bash
    python sp_pifo.py
    ```

### Example
```python
from sp_pifo import Packet, SPPIFOQueue

# Create a queue
queue = SPPIFOQueue()

# Enqueue packets
queue.enqueue(Packet(priority=1, arrival_time=0, data="Packet A"))
queue.enqueue(Packet(priority=2, arrival_time=1, data="Packet B"))

# Dequeue packets
packet = queue.dequeue()
print(f"Dequeued: {packet.data}")
```

## Output
The script provides detailed logs showing:
- Packets being enqueued with their attributes.
- The state of the queue after each operation.
- Packets being dequeued in priority order.

## Customization
You can modify the following parameters in the script:
- **Priority Levels**: Adjust the range of priorities for packets.
- **Queue Size**: Set a maximum size for the queue (if needed).
- **Packet Attributes**: Extend the `Packet` class to include additional metadata.

## Limitations
- Assumes a single-threaded environment; not optimized for concurrent access.
- Does not handle dynamic priority changes after enqueueing.

## Future Enhancements
- Add support for weighted priorities.
- Implement multi-threaded access with locking mechanisms.
- Extend to support real-time packet processing scenarios.
- Intelligent enqueuing

## Conclusion
The `sp_pifo.py` script is a simple yet powerful implementation of the SP-PIFO scheduling algorithm. It is ideal for educational purposes and as a foundation for more complex networking simulations.

For further details, refer to the code comments and inline documentation.

## References
- https://www.usenix.org/conference/nsdi20/presentation/alcoz
