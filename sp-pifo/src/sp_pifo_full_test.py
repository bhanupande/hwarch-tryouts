# ============================================================
# SPPifo Testing
# Author: Bhanu Pande
# Date: May 2, 2025
# Description: This script tests the SPPifo class by simulating a queuing system with multiple queues and configurable priorities.
# It generates random incoming data, enqueues it into the SPPifo instance, and then dequeues the data to check for unordered entries.
# ============================================================
from sp_pifo import SPPifo
import csv
import random
import time
import numpy as np
import matplotlib.pyplot as plt
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
from statistics import mean, stdev, median

def count_unordered_entries (outgoing_data):
    sorted_data = sorted(outgoing_data)
    unordered_count = sum (0 for i, val in enumerate(outgoing_data) if val != sorted_data[i])
    return unordered_count

def simulate_variation(N, NData, max_M, incoming_data):
    sppifo_results = {m: [] for m in range(0, max_M)}  # Start from M=0 to match the main script

    for M in range(1, max_M):  # Skip M=0 as it's invalid
        sppifoq = SPPifo(M, N, LEN=64)
        sppifoq_outgoing_data = []

        for data in incoming_data:
            sppifoq.enqueue(data)
        
        while True:
            try:
                sppifoq_outgoing_data.append(sppifoq.dequeue())
            except Exception as e:
                break
        
        sppifo_unordered_count = count_unordered_entries(sppifoq_outgoing_data)
        sppifo_results[M].append(sppifo_unordered_count / NData * 100)
    return sppifo_results

if __name__ == "__main__":
    N = 15
    num_variations = 10
    max_M = 15
    NData_start = 10
    NData_end = 100000
    random.seed(42)  # Set a seed for reproducibility

    NData_values = np.logspace(np.log10(NData_start), np.log10(NData_end), num_variations, dtype=int)

    all_results = {}

    for NData in NData_values:
        incoming_data = [random.randint(1, N) for _ in range(NData)]  # Generate random incoming data
        sppifo_results = simulate_variation(N, NData, max_M, incoming_data)

        for M, unordered_counts in sppifo_results.items():
            if M not in all_results:
                all_results[M] = []
            all_results[M].extend(unordered_counts)

    # Plot the scatter plot
    plt.figure(figsize=(12, 8))
    for M, counts in all_results.items():
        if not counts:  # Skip if counts list is empty
            continue

        x_values = [M] * len(counts)  # Use M as the x-coordinate for all points
        plt.scatter(x_values, counts, label=f"M={M}", alpha=0.6)

        # Annotate mean and median
        mean_value = mean(counts)
        median_value = median(counts)
        plt.annotate(f"Mean: {mean_value:.2f}", (M, mean_value), textcoords="offset points", xytext=(5, 5), ha='center', fontsize=8, color='blue')
        plt.annotate(f"Median: {median_value:.2f}", (M, median_value), textcoords="offset points", xytext=(5, -10), ha='center', fontsize=8, color='green')

    plt.xlabel("M (Number of Queues)")
    plt.ylabel("Unordered Count (%)")
    plt.title("Scatter Plot of Unordered Counts vs M")
    plt.grid(True, linestyle='--', alpha=0.7)
    plt.legend(title="M Values", bbox_to_anchor=(1.05, 1), loc='upper left')
    plt.tight_layout()

    # Save the figure
    plt.savefig("unordered_counts_vs_M.png")
    plt.show()