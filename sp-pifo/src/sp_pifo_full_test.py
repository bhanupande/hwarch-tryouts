# ============================================================
# SPPifo Testing
# Author: Bhanu Pande
# Date: May 2, 2025
# Description: This script tests the SPPifo class by simulating a queuing system with multiple queues and configurable priorities.
# It generates random incoming data, enqueues it into the SPPifo instance, and then dequeues the data to check for unordered entries.
# ============================================================

# Importing necessary libraries and modules
from sp_pifo import SPPifo  # Import the SPPifo class to simulate the queuing system
import csv  # For potential CSV file operations (not used in this script)
import random  # For generating random incoming data
import time  # For potential timing operations (not used in this script)
import numpy as np  # For numerical operations, such as generating logarithmic spaced values
import matplotlib.pyplot as plt  # For plotting results
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed  # For parallel processing (not used in this script)
from statistics import mean, stdev, median  # For statistical calculations
import os  # Import the os module to handle file paths

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
    unordered_count = sum(1 for i, val in enumerate(outgoing_data) if val != sorted_data[i])  # Count mismatches
    return unordered_count

# Function to simulate variations in the queuing system
def simulate_variation(N, NData, max_M, incoming_data):
    """
    Simulates the SPPifo queuing system for different numbers of queues (M) and calculates the percentage of unordered entries.

    Parameters:
    N (int): The range of random data values (1 to N).
    NData (int): The number of data points to generate.
    max_M (int): The maximum number of queues to simulate.
    incoming_data (list): The list of incoming data to enqueue.

    Returns:
    dict: A dictionary where keys are M values and values are lists of unordered percentages.
    """
    sppifo_results = {m: [] for m in range(0, max_M)}  # Initialize results dictionary for each M value

    for M in range(1, max_M):  # Iterate over M values (starting from 1, as M=0 is invalid)
        sppifoq = SPPifo(M, N, LEN=64)  # Create an SPPifo instance with M queues, N priorities, and a queue length of 64
        sppifoq_outgoing_data = []  # List to store dequeued data

        # Enqueue all incoming data into the SPPifo instance
        for data in incoming_data:
            sppifoq.enqueue(data)
        
        # Dequeue all data until the queue is empty
        while True:
            try:
                sppifoq_outgoing_data.append(sppifoq.dequeue())
            except Exception as e:  # Break the loop when the queue is empty
                break
        
        # Calculate the percentage of unordered entries
        sppifo_unordered_count = count_unordered_entries(sppifoq_outgoing_data)
        sppifo_results[M].append(sppifo_unordered_count / NData * 100)  # Store the percentage
    return sppifo_results

# Main script execution
if __name__ == "__main__":
    # Configuration parameters
    N = 15  # Range of random data values (1 to N)
    num_variations = 10  # Number of variations for NData
    max_M = 15  # Maximum number of queues to simulate
    NData_start = 10  # Starting value for NData
    NData_end = 100000  # Ending value for NData
    random.seed(42)  # Set a seed for reproducibility of random data

    # Generate logarithmically spaced values for NData
    NData_values = np.logspace(np.log10(NData_start), np.log10(NData_end), num_variations, dtype=int)

    all_results = {}  # Dictionary to store results for all M values

    # Iterate over each NData value
    for NData in NData_values:
        # Generate random incoming data
        incoming_data = [random.randint(1, N) for _ in range(NData)]
        # Simulate the queuing system for the current NData value
        sppifo_results = simulate_variation(N, NData, max_M, incoming_data)

        # Aggregate results for each M value
        for M, unordered_counts in sppifo_results.items():
            if M not in all_results:
                all_results[M] = []
            all_results[M].extend(unordered_counts)

    # Plot the scatter plot of unordered counts vs M
    plt.figure(figsize=(12, 8))  # Set the figure size
    for M, counts in all_results.items():
        if not counts:  # Skip if the counts list is empty
            continue

        x_values = [M] * len(counts)  # Use M as the x-coordinate for all points
        plt.scatter(x_values, counts, label=f"M={M}", alpha=0.6)  # Scatter plot for the current M value

        # Annotate mean and median values on the plot
        mean_value = mean(counts)
        median_value = median(counts)
        plt.annotate(f"Mean: {mean_value:.2f}", (M, mean_value), textcoords="offset points", xytext=(5, 5), ha='center', fontsize=8, color='blue')
        plt.annotate(f"Median: {median_value:.2f}", (M, median_value), textcoords="offset points", xytext=(5, -10), ha='center', fontsize=8, color='green')

    # Add labels, title, and grid to the plot
    plt.xlabel("M (Number of Queues)")
    plt.ylabel("Unordered Count (%)")
    plt.title("Scatter Plot of Unordered Counts vs M")
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(title="M Values", bbox_to_anchor=(1.05, 1), loc='upper left')  # Place the legend outside the plot
    plt.tight_layout()  # Adjust layout to prevent overlap

    # Save the plot as an image file in the same directory as the script
    script_dir = os.path.dirname(os.path.abspath(__file__))  # Get the directory of the current script
    output_path = os.path.join(script_dir, "unordered_counts_vs_M.png")  # Construct the full path for the output file
    plt.savefig(output_path)  # Save the plot to the specified path
    plt.show()  # Display the plot