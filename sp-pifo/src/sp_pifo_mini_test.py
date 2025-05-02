# ============================================================
# SPPifo Testing (Simplified for M Sweep)
# Author: Bhanu Pande
# Date: May 3, 2025
# Description: This script tests the SPPifo class by sweeping values of M (number of queues) and calculating the percentage of unordered entries.
# ============================================================

# Importing necessary libraries and modules
from sp_pifo import SPPifo  # Import the SPPifo class to simulate the queuing system
import random  # For generating random incoming data
import matplotlib.pyplot as plt  # For plotting results
from statistics import mean, median  # For statistical calculations

# Function to count unordered entries in the outgoing data
def count_unordered_entries(outgoing_data):
    """
    Counts the number of unordered entries in the outgoing data compared to a sorted version of the data.

    Parameters:
    outgoing_data (list): The list of dequeued data.

    Returns:
    int: The count of unordered entries.
    """
    sorted_data = sorted(outgoing_data)  # Create a sorted version of the data
    print(f"Sorted data: {sorted_data}")  # Print the sorted data for debugging
    print(f"Outgoing data: {outgoing_data}")  # Print the outgoing data for debugging
    unordered_count = sum(1 for i, val in enumerate(outgoing_data) if val != sorted_data[i])  # Count mismatches
    print(f"Unordered entries count: {unordered_count}")  # Print the count of unordered entries
    return unordered_count

# Function to simulate the queuing system for a given M value
def simulate_for_M(M, N, incoming_data):
    """
    Simulates the SPPifo queuing system for a specific number of queues (M) and calculates the percentage of unordered entries.

    Parameters:
    M (int): The number of queues.
    N (int): The range of random data values (1 to N).
    incoming_data (list): The list of incoming data to enqueue.

    Returns:
    tuple: Outgoing data, percentage of unordered entries, and latency list.
    """
    sppifoq = SPPifo(M, N, LEN=64)  # Create an SPPifo instance with M queues, N priorities, and a queue length of 64
    sppifoq_outgoing_data = []  # List to store dequeued data
    latency_list = []  # List to store latency for each data item
    enqueue_ticks = {}  # Dictionary to store enqueue tick for each data item

    # Enqueue all incoming data into the SPPifo instance
    for data in incoming_data:
        enqueue_ticks[data] = sppifoq.ticks  # Record the tick count at enqueue
        sppifoq.enqueue(data)
    
    # Dequeue all data until the queue is empty
    while True:
        try:
            dequeued_data = sppifoq.dequeue()
            sppifoq_outgoing_data.append(dequeued_data)
            latency = sppifoq.ticks - enqueue_ticks[dequeued_data]  # Calculate latency
            latency_list.append(latency)
        except Exception:  # Break the loop when the queue is empty
            print("Queue is empty, stopping dequeue operation.")
            break
    
    # Calculate the percentage of unordered entries
    sppifo_unordered_count = count_unordered_entries(sppifoq_outgoing_data)
    return sppifoq_outgoing_data, sppifo_unordered_count / len(incoming_data) * 100, latency_list

# Main script execution
if __name__ == "__main__":
    # Configuration parameters
    N = 15  # Range of random data values (1 to N)
    NData = 20  # Fixed number of data points to generate
    max_M = 15  # Maximum number of queues to simulate
    random.seed(42)  # Set a seed for reproducibility of random data

    # Generate random incoming data
    incoming_data = [random.randint(1, N) for _ in range(NData)]

    x, y, latencies = simulate_for_M(2, N, incoming_data)  # Run the simulation for M=2
    print(f"Incoming data: {incoming_data}")  # Print the generated incoming data
    print(f"Outgoing data: {x}")  # Print the outgoing data
    print(f"Unordered entries percentage for M=2: {y:.2f}%")  # Print the unordered entries percentage for M=2
    print(f"Latencies: {latencies}")  # Print the latency list
    print(f"Average latency: {mean(latencies):.2f} ticks")  # Print the average latency
    print(f"Median latency: {median(latencies):.2f} ticks")  # Print the median latency


