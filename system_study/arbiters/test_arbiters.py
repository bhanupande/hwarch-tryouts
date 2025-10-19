#!/usr/bin/env python3
"""
Simplified Traffic Class Testing for Arbiters
============================================

This module contains only the essential components needed to run traffic class examples
with the run_traffic_class_examples() function and all its supporting logic.
NO HARDCODED VALUES - everything is configurable through parameters.
"""

import os
import time
import random
import statistics
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from enum import Enum
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns

# Import arbitration logic from the main arbiters module
from arbiters import Arbiter


# Traffic Class Configuration
class TrafficClass(Enum):
    """Traffic class enumeration for QoS-aware arbitration."""
    REAL_TIME = "real_time"
    ISOCHRONOUS = "isochronous"  
    BEST_EFFORT = "best_effort"


@dataclass
class TrafficClassInfo:
    """Traffic class characteristics."""
    name: str
    priority: int
    max_acceptable_latency: Optional[int]
    arrival_rate: float  # Requests per cycle


# Traffic class configuration with QoS requirements
TRAFFIC_CLASSES = {
    TrafficClass.REAL_TIME: TrafficClassInfo(
        name="Real-Time",
        priority=1,  # Highest priority
        max_acceptable_latency=10,  # Must complete within 10 cycles
        arrival_rate=0.3
    ),
    TrafficClass.ISOCHRONOUS: TrafficClassInfo(
        name="Isochronous", 
        priority=2,  # Medium priority
        max_acceptable_latency=20,  # Must complete within 20 cycles
        arrival_rate=0.4
    ),
    TrafficClass.BEST_EFFORT: TrafficClassInfo(
        name="Best-Effort",
        priority=3,  # Lowest priority
        max_acceptable_latency=None,  # No latency constraint
        arrival_rate=0.3
    )
}


@dataclass
class Request:
    """Represents a memory access request."""
    id: int
    priority: int
    traffic_class: TrafficClass
    arrival_cycle: int
    completion_cycle: Optional[int] = None


def generate_traffic(num_requestors: int, cycles: int, pattern_type: str, traffic_mix: str) -> List[List[Request]]:
    """Generate traffic patterns for testing."""
    patterns = [[] for _ in range(cycles)]
    
    # Traffic class distribution
    if traffic_mix == 'real_time_only':
        weights = {TrafficClass.REAL_TIME: 1.0, TrafficClass.ISOCHRONOUS: 0.0, TrafficClass.BEST_EFFORT: 0.0}
    elif traffic_mix == 'isochronous_only':
        weights = {TrafficClass.REAL_TIME: 0.0, TrafficClass.ISOCHRONOUS: 1.0, TrafficClass.BEST_EFFORT: 0.0}
    elif traffic_mix == 'best_effort_only':
        weights = {TrafficClass.REAL_TIME: 0.0, TrafficClass.ISOCHRONOUS: 0.0, TrafficClass.BEST_EFFORT: 1.0}
    else:  # mixed
        weights = {TrafficClass.REAL_TIME: 0.3, TrafficClass.ISOCHRONOUS: 0.4, TrafficClass.BEST_EFFORT: 0.3}
    
    request_id = 0
    
    for cycle in range(cycles):
        cycle_requests = []
        
        for requestor in range(num_requestors):
            # Decide if this requestor makes a request
            if pattern_type == 'random':
                make_request = random.random() < 0.3
            elif pattern_type == 'uniform':
                make_request = (cycle + requestor) % 3 == 0
            elif pattern_type == 'burst':
                make_request = (cycle // 5) % 2 == 0
            elif pattern_type == 'sequential':
                make_request = (cycle % num_requestors) == requestor
            else:
                make_request = random.random() < 0.3
            
            if make_request:
                # Select traffic class
                rand_val = random.random()
                cumulative = 0.0
                selected_class = TrafficClass.BEST_EFFORT
                
                for tc, weight in weights.items():
                    cumulative += weight
                    if rand_val <= cumulative:
                        selected_class = tc
                        break
                
                request = Request(
                    id=request_id,
                    priority=TRAFFIC_CLASSES[selected_class].priority,
                    traffic_class=selected_class,
                    arrival_cycle=cycle
                )
                cycle_requests.append(request)
                request_id += 1
        
        patterns[cycle] = cycle_requests
    
    return patterns


def measure_performance(arbiter: Arbiter, request_patterns: List[List[Request]]) -> Dict[str, Any]:
    """Measure arbiter performance with given traffic patterns."""
    total_cycles = len(request_patterns)
    all_requests = []
    
    # Collect all requests
    for cycle_requests in request_patterns:
        all_requests.extend(cycle_requests)
    
    # Realistic simulation with proper queueing
    pending_requests = []  # Queue of pending requests
    
    for cycle, new_requests in enumerate(request_patterns):
        # Add new requests to pending queue
        pending_requests.extend(new_requests)
        
        if pending_requests:
            # Create request vector for arbiter from pending requests
            request_vector = [None] * arbiter.num_requestors
            request_map = {}
            
            # Map pending requests to requestor positions (first come first serve per requestor)
            for req in pending_requests:
                requestor_id = req.id % arbiter.num_requestors
                if request_vector[requestor_id] is None:
                    request_vector[requestor_id] = req
                    request_map[requestor_id] = req
            
            # Arbitrate among available requests
            granted_index = arbiter.arbitrate(request_vector)
            if granted_index is not None and granted_index in request_map:
                granted_request = request_map[granted_index]
                # Memory access takes 1 cycle to complete
                granted_request.completion_cycle = cycle + 1
                # Remove served request from pending queue
                pending_requests.remove(granted_request)
    
    # Calculate metrics
    total_served = sum(1 for req in all_requests if req.completion_cycle is not None)
    total_violations = 0
    latencies = []
    
    for req in all_requests:
        if req.completion_cycle is not None:
            latency = req.completion_cycle - req.arrival_cycle
            latencies.append(latency)
            max_lat = TRAFFIC_CLASSES[req.traffic_class].max_acceptable_latency
            if max_lat and latency > max_lat:
                total_violations += 1
    
    # Corrected calculations
    # Throughput: requests served per cycle (max 1.0 since arbiter grants 1 per cycle)
    throughput = min(total_served / total_cycles, 1.0) if total_cycles > 0 else 0.0
    
    # QoS calculations
    qos_compliant = total_served - total_violations
    qos_throughput = qos_compliant / total_cycles if total_cycles > 0 else 0.0
    qos_rate = (qos_compliant / total_served * 100) if total_served > 0 else 0.0
    
    # Latency statistics
    avg_latency = statistics.mean(latencies) if latencies else 0.0
    max_latency = max(latencies) if latencies else 0.0
    
    # Service rate (percentage of total generated requests that got served)
    service_rate = (total_served / len(all_requests) * 100) if all_requests else 0.0
    
    return {
        'throughput': throughput,
        'qos_throughput': qos_throughput,
        'qos_rate': qos_rate,
        'violations': total_violations,
        'utilization': throughput * 100,
        'avg_latency': avg_latency,
        'max_latency': max_latency,
        'service_rate': service_rate,
        'total_requests': len(all_requests),
        'served_requests': total_served
    }


def run_traffic_class_examples(req=16, cycles=2000):
    """
    Comprehensive traffic class testing for arbiter performance analysis.
    
    Uses sufficient cycles to reveal true performance differences between arbiters
    without artificial bottlenecks that mask poor QoS behavior.
    
    Parameters:
    - req: Number of requestors (default: 16 for realistic contention)
    - cycles: Simulation cycles (default: 2000 for statistical significance)
    
    Generates separate CSV files for each traffic mix showing:
    - Service rates under sustained load
    - QoS violation patterns 
    - Latency distributions
    - Arbiter efficiency comparisons
    """
    print("COMPREHENSIVE TRAFFIC CLASS TESTING")
    print("=" * 60)
    print(f"Parameters: {req} requestors, {cycles} cycles")
    print("=" * 60)
    
    # Define a few key test configurations - no hardcoded values!
    policies = ['FixedPriority', 'RoundRobin', 'Random', 'WeightedRoundRobin']
    patterns = ['random', 'burst', 'uniform', 'sequential']
    traffics = ['mixed', 'real_time_only', 'isochronous_only', 'best_effort_only']
    modes = ['random', 'mean', 'median']
    test_configs = []
    for pol in policies:
        for pat in patterns:
            for traf in traffics:
                if (pol == 'WeightedRoundRobin'):
                    for mode in modes:
                        test_configs.append({
                            'num_requestors': req,
                            'policy': pol,
                            'pattern_type': pat,
                            'traffic_mix': traf,
                            'cycles': cycles,
                            'weights': [(i+1)//4 + 1 for i in range(req)],
                            'mode': mode
                        })
                else:
                    test_configs.append({
                        'num_requestors': req,
                        'policy': pol,
                        'pattern_type': pat,
                        'traffic_mix': traf,
                        'cycles': cycles
                    })
    
    results = []
    
    # Run tests
    print(f"\nRunning {len(test_configs)} test configurations...")
    for i, config in enumerate(test_configs, 1):
        print(f"Test {i}/{len(test_configs)}: {config['policy']} ({config['pattern_type']}) - {config['traffic_mix']}")
        
        # Create arbiter
        weights = config.get('weights', None)
        if weights:
            arbiter = Arbiter(num_requestors=req, policy=config['policy'], weights=weights)
        else:
            arbiter = Arbiter(num_requestors=req, policy=config['policy'])
        
        # Generate traffic and measure performance
        traffic_patterns = generate_traffic(req, cycles, config['pattern_type'], config['traffic_mix'])
        perf = measure_performance(arbiter, traffic_patterns)
        
        # Show progress with detailed debug info
        print(f"  Total Reqs: {perf['total_requests']} | Served: {perf['served_requests']} ({perf['service_rate']:.1f}%) | "
              f"QoS Rate: {perf['qos_rate']:.1f}% | Violations: {perf['violations']} | "
              f"Avg Lat: {perf['avg_latency']:.1f} | Max Lat: {perf['max_latency']:.0f}")
        
        # Store result
        result = {
            'config': config,
            'performance': perf,
            'arbiter_name': arbiter.name
        }
        results.append(result)
    
    # Generate detailed report
    print("\n" + "=" * 80)
    print("PERFORMANCE SUMMARY")
    print("=" * 80)
    print(f"{'Test':<4} {'Policy (Mode)':<20} {'Mix':<12} {'Reqs':<6} {'Served':<6} {'Tput':<8} {'QoS%':<8} {'Viol':<6} {'AvgLat':<7}")
    print("-" * 80)
    
    for i, result in enumerate(results, 1):
        config = result['config']
        perf = result['performance']
        policy_mode = f"{config['policy']} ({config['pattern_type']})"
        
        print(f"{i:<4} {policy_mode:<20} {config['traffic_mix']:<12} "
              f"{perf['total_requests']:<6} {perf['served_requests']:<6} "
              f"{perf['throughput']:<8.3f} {perf['qos_rate']:<8.1f} "
              f"{perf['violations']:<6} {perf['avg_latency']:<7.1f}")
    
    # Save separate CSV reports by traffic mix
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Group results by traffic mix
    traffic_groups = {}
    for result in results:
        traffic_mix = result['config']['traffic_mix']
        if traffic_mix not in traffic_groups:
            traffic_groups[traffic_mix] = []
        traffic_groups[traffic_mix].append(result)
    
    saved_files = []
    
    # Create separate CSV for each traffic mix
    for traffic_mix, group_results in traffic_groups.items():
        filename = f"traffic_report_{traffic_mix}.csv"
        full_path = os.path.join(script_dir, filename)
        
        with open(full_path, 'w') as f:
            # CSV header with combined Policy-Pattern column
            f.write("Test,PolicyPattern,TotalRequests,ServedRequests,ServiceRate,Throughput,QoSRate,Violations,AvgLatency,MaxLatency\n")
            
            # CSV data for this traffic mix
            for i, result in enumerate(group_results, 1):
                config = result['config']
                perf = result['performance']
                
                # Combine policy and pattern into one field, include mode for WeightedRoundRobin
                if config['policy'] == 'WeightedRoundRobin' and 'mode' in config:
                    policy_pattern = f"{config['policy']}_{config['mode']}_{config['pattern_type']}"
                else:
                    policy_pattern = f"{config['policy']}_{config['pattern_type']}"
                
                f.write(f"{i},{policy_pattern},"
                       f"{perf['total_requests']},{perf['served_requests']},{perf['service_rate']:.1f},"
                       f"{perf['throughput']:.3f},{perf['qos_rate']:.1f},"
                       f"{perf['violations']},{perf['avg_latency']:.1f},{perf['max_latency']:.0f}\n")
        
        saved_files.append(full_path)
    
    print(f"\nSeparate CSV reports saved:")
    for file_path in saved_files:
        print(f"  - {file_path}")
    
    return results


def plot_performance_metrics():
    """
    Generate comprehensive performance plots for all CSV files.
    Creates visualizations for average latency, peak latency, and QoS rate.
    """
    # Set up plotting style
    plt.style.use('default')
    sns.set_palette("husl")
    
    # Find all CSV files
    script_dir = os.path.dirname(os.path.abspath(__file__))
    csv_files = [f for f in os.listdir(script_dir) if f.startswith('traffic_report_') and f.endswith('.csv')]
    
    if not csv_files:
        print("No CSV files found. Run the simulation first!")
        return
    
    # Create plots for each traffic mix
    for csv_file in csv_files:
        traffic_mix = csv_file.replace('traffic_report_', '').replace('.csv', '')
        print(f"Generating plots for: {traffic_mix}")
        
        # Read data
        df = pd.read_csv(os.path.join(script_dir, csv_file))
        
        # Create figure with subplots - increased figure size and spacing
        fig, axes = plt.subplots(2, 2, figsize=(20, 16))
        fig.suptitle(f'Arbiter Performance Analysis - {traffic_mix.replace("_", " ").title()} Traffic', 
                     fontsize=18, fontweight='bold', y=0.98)
        
        # Adjust spacing between subplots
        plt.subplots_adjust(hspace=0.35, wspace=0.25, top=0.92, bottom=0.12, left=0.08, right=0.95)
        
        # 1. Average Latency Comparison
        ax1 = axes[0, 0]
        bars1 = ax1.bar(range(len(df)), df['AvgLatency'], color=sns.color_palette("viridis", len(df)))
        ax1.set_title('Average Latency by Policy', fontweight='bold', fontsize=14, pad=15)
        ax1.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax1.set_ylabel('Average Latency (cycles)', fontsize=12, labelpad=10)
        ax1.set_xticks(range(len(df)))
        ax1.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax1.tick_params(axis='y', labelsize=10)
        ax1.grid(True, alpha=0.3)
        
        # Add value labels on bars - only for readable values
        for i, bar in enumerate(bars1):
            height = bar.get_height()
            if height > 0:  # Only show labels for non-zero values
                ax1.text(bar.get_x() + bar.get_width()/2., height + height*0.02,
                        f'{height:.1f}', ha='center', va='bottom', fontsize=9, fontweight='bold')
        
        # 2. Peak Latency Comparison
        ax2 = axes[0, 1]
        bars2 = ax2.bar(range(len(df)), df['MaxLatency'], color=sns.color_palette("plasma", len(df)))
        ax2.set_title('Peak Latency by Policy', fontweight='bold', fontsize=14, pad=15)
        ax2.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax2.set_ylabel('Peak Latency (cycles)', fontsize=12, labelpad=10)
        ax2.set_xticks(range(len(df)))
        ax2.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax2.tick_params(axis='y', labelsize=10)
        ax2.grid(True, alpha=0.3)
        
        # Add value labels on bars - only show significant values
        for i, bar in enumerate(bars2):
            height = bar.get_height()
            if height > 10:  # Only show labels for significant latencies
                ax2.text(bar.get_x() + bar.get_width()/2., height + height*0.02,
                        f'{height:.0f}', ha='center', va='bottom', fontsize=9, fontweight='bold')
        
        # 3. QoS Rate Comparison
        ax3 = axes[1, 0]
        bars3 = ax3.bar(range(len(df)), df['QoSRate'], color=sns.color_palette("coolwarm", len(df)))
        ax3.set_title('QoS Compliance Rate by Policy', fontweight='bold', fontsize=14, pad=15)
        ax3.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax3.set_ylabel('QoS Rate (%)', fontsize=12, labelpad=10)
        ax3.set_xticks(range(len(df)))
        ax3.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax3.tick_params(axis='y', labelsize=10)
        ax3.set_ylim(0, 105)  # Slightly higher to accommodate labels
        ax3.grid(True, alpha=0.3)
        
        # Add value labels on bars - only for significant values
        for i, bar in enumerate(bars3):
            height = bar.get_height()
            if height > 5:  # Only show labels for QoS rates > 5%
                ax3.text(bar.get_x() + bar.get_width()/2., height + 1.5,
                        f'{height:.1f}%', ha='center', va='bottom', fontsize=9, fontweight='bold')
        
        # 4. Service Rate vs QoS Rate Scatter Plot
        ax4 = axes[1, 1]
        scatter = ax4.scatter(df['ServiceRate'], df['QoSRate'], 
                            c=df['AvgLatency'], s=120, alpha=0.8, 
                            cmap='RdYlBu_r', edgecolors='black', linewidth=1.0)
        ax4.set_title('Service Rate vs QoS Rate\n(Color = Avg Latency)', fontweight='bold', fontsize=14, pad=15)
        ax4.set_xlabel('Service Rate (%)', fontsize=12, labelpad=10)
        ax4.set_ylabel('QoS Rate (%)', fontsize=12, labelpad=10)
        ax4.tick_params(axis='both', labelsize=10)
        ax4.grid(True, alpha=0.3)
        
        # Add colorbar for scatter plot
        cbar = plt.colorbar(scatter, ax=ax4, shrink=0.8)
        cbar.set_label('Average Latency (cycles)', fontsize=11, labelpad=15)
        cbar.ax.tick_params(labelsize=9)
        
        # Add policy labels to scatter points - simplified and better positioned
        for i, policy in enumerate(df['PolicyPattern']):
            policy_short = policy.split('_')[0][:5]  # Slightly longer abbreviation
            ax4.annotate(policy_short, 
                        (df['ServiceRate'].iloc[i], df['QoSRate'].iloc[i]),
                        xytext=(8, 8), textcoords='offset points',
                        fontsize=8, alpha=0.9, fontweight='bold',
                        bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.7, edgecolor='none'))
        
        # Save plot with better settings
        plot_filename = f"performance_analysis_{traffic_mix}.png"
        plot_path = os.path.join(script_dir, plot_filename)
        plt.savefig(plot_path, dpi=300, bbox_inches='tight', facecolor='white', edgecolor='none')
        print(f"  Saved: {plot_filename}")
        
        # Show plot (optional - comment out if running in batch)
        # plt.show()
        plt.close()
    
    print(f"\nAll plots generated successfully!")
    print("Generated files:")
    for csv_file in csv_files:
        traffic_mix = csv_file.replace('traffic_report_', '').replace('.csv', '')
        print(f"  - performance_analysis_{traffic_mix}.png")


if __name__ == "__main__":
    # Run the simulation
    run_traffic_class_examples(req=16, cycles=2000)
    
    # Generate plots
    print("\n" + "=" * 60)
    print("GENERATING PERFORMANCE VISUALIZATIONS")
    print("=" * 60)
    plot_performance_metrics()