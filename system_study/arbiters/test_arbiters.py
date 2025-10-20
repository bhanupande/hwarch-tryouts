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
    base_priority: int
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
                
                # Calculate base priority based on traffic class and some variation
                # Base priority should be stable for each request throughout its lifetime
                # NOTE: Lower numerical values = Higher priority (like Unix nice values)
                traffic_class_info = TRAFFIC_CLASSES[selected_class]
                base_base_priority = traffic_class_info.priority
                
                # Add some variation within traffic class to make it more realistic
                # Since lower values = higher priority, we subtract variation for higher priority classes
                # Real-time: base priority 1, variation 0-2 (range 1-3, but inverted to -1 to 1)
                # Isochronous: base priority 2, variation 0-3 (range 2-5, but inverted to -1 to 2) 
                # Best-effort: base priority 3, variation 0-4 (range 3-7, but inverted to -1 to 3)
                if selected_class == TrafficClass.REAL_TIME:
                    # Higher priority traffic gets lower base priority values
                    priority_variation = random.randint(-1, 1)  # Most critical, stay close to 1
                elif selected_class == TrafficClass.ISOCHRONOUS:
                    priority_variation = random.randint(-1, 2)  # Medium priority range
                else:  # BEST_EFFORT
                    priority_variation = random.randint(-1, 3)  # Lowest priority, higher numbers
                
                calculated_base_priority = base_base_priority + priority_variation
                
                request = Request(
                    id=request_id,
                    priority=traffic_class_info.priority,  # Keep original priority for QoS tracking
                    traffic_class=selected_class,
                    arrival_cycle=cycle,
                    base_priority=calculated_base_priority
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
            base_priority_vector = [0] * arbiter.num_requestors
            request_map = {}
            
            # Map pending requests to requestor positions (first come first serve per requestor)
            for req in pending_requests:
                requestor_id = req.id % arbiter.num_requestors
                if request_vector[requestor_id] is None:
                    request_vector[requestor_id] = req
                    base_priority_vector[requestor_id] = req.base_priority
                    request_map[requestor_id] = req
            
            # Convert request_vector to boolean vector for arbiter
            boolean_request_vector = [req is not None for req in request_vector]
            
            # Arbitrate among available requests
            granted_index = arbiter.arbitrate(boolean_request_vector, base_priority_vector)
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
    
    # Starvation analysis: categorize requests by traffic class
    starvation_by_class = {
        TrafficClass.REAL_TIME: {'served': [], 'starved': []},
        TrafficClass.ISOCHRONOUS: {'served': [], 'starved': []},
        TrafficClass.BEST_EFFORT: {'served': [], 'starved': []}
    }
    
    for req in all_requests:
        if req.completion_cycle is not None:
            latency = req.completion_cycle - req.arrival_cycle
            latencies.append(latency)
            starvation_by_class[req.traffic_class]['served'].append(latency)
            max_lat = TRAFFIC_CLASSES[req.traffic_class].max_acceptable_latency
            if max_lat and latency > max_lat:
                total_violations += 1
        else:
            # Request was starved (never served)
            starvation_by_class[req.traffic_class]['starved'].append(req)
    
    # Calculate starvation metrics
    total_starved = sum(1 for req in all_requests if req.completion_cycle is None)
    starvation_rate = (total_starved / len(all_requests) * 100) if all_requests else 0.0
    
    # Calculate fairness metrics - coefficient of variation of service by traffic class
    service_by_class = []
    for tc_info in starvation_by_class.values():
        served_count = len(tc_info['served'])
        service_by_class.append(served_count)
    
    # Fairness index (lower is more unfair, 1.0 is perfectly fair)
    if len(service_by_class) > 1 and any(service_by_class):
        mean_service = statistics.mean(service_by_class)
        if mean_service > 0:
            cv_service = statistics.stdev(service_by_class) / mean_service
            fairness_index = 1.0 / (1.0 + cv_service)  # Normalized fairness (0-1)
        else:
            fairness_index = 0.0
    else:
        fairness_index = 1.0
    
    # Class-specific starvation rates
    rt_starved = len(starvation_by_class[TrafficClass.REAL_TIME]['starved'])
    iso_starved = len(starvation_by_class[TrafficClass.ISOCHRONOUS]['starved'])
    be_starved = len(starvation_by_class[TrafficClass.BEST_EFFORT]['starved'])
    
    # Calculate total requests per traffic class for starvation rate calculation
    rt_total = rt_starved + len(starvation_by_class[TrafficClass.REAL_TIME]['served'])
    iso_total = iso_starved + len(starvation_by_class[TrafficClass.ISOCHRONOUS]['served'])
    be_total = be_starved + len(starvation_by_class[TrafficClass.BEST_EFFORT]['served'])
    
    rt_starvation_rate = (rt_starved / rt_total * 100) if rt_total > 0 else 0.0
    iso_starvation_rate = (iso_starved / iso_total * 100) if iso_total > 0 else 0.0
    be_starvation_rate = (be_starved / be_total * 100) if be_total > 0 else 0.0
    
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
        'served_requests': total_served,
        'starvation_rate': starvation_rate,
        'fairness_index': fairness_index,
        'rt_starvation_rate': rt_starvation_rate,
        'iso_starvation_rate': iso_starvation_rate,
        'be_starvation_rate': be_starvation_rate,
        'total_starved': total_starved
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
    policies = ['FixedPriority', 'WeightedRoundRobin', 'DynamicPriority']#, 'Random', 'WeightedRandom']
    patterns = ['random', 'burst', 'uniform', 'sequential']
    traffics = ['mixed', 'real_time_only', 'isochronous_only', 'best_effort_only']
    modes = ['median']#, 'mean', 'random']
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
        
        # Show progress with detailed debug info including starvation
        print(f"  Total Reqs: {perf['total_requests']} | Served: {perf['served_requests']} ({perf['service_rate']:.1f}%) | "
              f"QoS Rate: {perf['qos_rate']:.1f}% | Violations: {perf['violations']} | "
              f"Avg Lat: {perf['avg_latency']:.1f} | Max Lat: {perf['max_latency']:.0f} | "
              f"Starvation: {perf['starvation_rate']:.1f}% | Fairness: {perf['fairness_index']:.3f}")
        
        # Store result
        result = {
            'config': config,
            'performance': perf,
            'arbiter_name': arbiter.name
        }
        results.append(result)
    
    # Generate detailed report
    print("\n" + "=" * 120)
    print("PERFORMANCE SUMMARY (with Starvation Analysis)")
    print("=" * 120)
    print(f"{'Test':<4} {'Policy (Mode)':<20} {'Mix':<12} {'Reqs':<6} {'Served':<6} {'Tput':<8} {'QoS%':<8} {'Viol':<6} {'AvgLat':<7} {'Starv%':<7} {'Fair':<6}")
    print("-" * 120)
    
    for i, result in enumerate(results, 1):
        config = result['config']
        perf = result['performance']
        policy_mode = f"{config['policy']} ({config['pattern_type']})"
        
        print(f"{i:<4} {policy_mode:<20} {config['traffic_mix']:<12} "
              f"{perf['total_requests']:<6} {perf['served_requests']:<6} "
              f"{perf['throughput']:<8.3f} {perf['qos_rate']:<8.1f} "
              f"{perf['violations']:<6} {perf['avg_latency']:<7.1f} "
              f"{perf['starvation_rate']:<7.1f} {perf['fairness_index']:<6.3f}")
    
    # Add starvation analysis summary
    print("\n" + "=" * 120)
    print("STARVATION ANALYSIS BY TRAFFIC CLASS")
    print("=" * 120)
    print("Legend: Starv% = Overall Starvation Rate, Fair = Fairness Index (1.0=perfect, 0.0=unfair)")
    print("RT=RealTime, Iso=Isochronous, BE=BestEffort starvation rates")
    print("-" * 120)
    
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
            f.write("Test,PolicyPattern,TotalRequests,ServedRequests,ServiceRate,Throughput,QoSRate,Violations,AvgLatency,MaxLatency,StarvationRate,FairnessIndex,RTStarvationRate,IsoStarvationRate,BEStarvationRate\n")
            
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
                       f"{perf['violations']},{perf['avg_latency']:.1f},{perf['max_latency']:.0f},"
                       f"{perf['starvation_rate']:.1f},{perf['fairness_index']:.3f},"
                       f"{perf['rt_starvation_rate']:.1f},{perf['iso_starvation_rate']:.1f},{perf['be_starvation_rate']:.1f}\n")
        
        saved_files.append(full_path)
    
    print(f"\nSeparate CSV reports saved:")
    for file_path in saved_files:
        print(f"  - {file_path}")
    
    return results


def plot_performance_metrics():
    """
    Generate comprehensive performance plots with combined subplots for each traffic mix.
    Creates 2x2 subplot layout for better comparison and overview.
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
    
    # Create combined plots for each traffic mix
    for csv_file in csv_files:
        traffic_mix = csv_file.replace('traffic_report_', '').replace('.csv', '')
        print(f"Generating combined plot for: {traffic_mix}")
        
        # Read data
        df = pd.read_csv(os.path.join(script_dir, csv_file))
        
        # Create figure with 2x3 subplots to include starvation metrics
        fig, axes = plt.subplots(2, 3, figsize=(24, 16))
        fig.suptitle(f'Arbiter Performance Analysis with Starvation Metrics - {traffic_mix.replace("_", " ").title()} Traffic', 
                     fontsize=18, fontweight='bold', y=0.98)
        
        # Adjust spacing between subplots
        plt.subplots_adjust(hspace=0.35, wspace=0.25, top=0.92, bottom=0.12, left=0.06, right=0.97)
        
        # 1. Average Latency Comparison (Top Left)
        ax1 = axes[0, 0]
        bars1 = ax1.bar(range(len(df)), df['AvgLatency'], color=sns.color_palette("viridis", len(df)))
        ax1.set_title('Average Latency by Policy', fontweight='bold', fontsize=14, pad=15)
        ax1.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax1.set_ylabel('Average Latency (cycles)', fontsize=12, labelpad=10)
        ax1.set_xticks(range(len(df)))
        ax1.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax1.tick_params(axis='y', labelsize=10)
        ax1.grid(True, alpha=0.3)
        
        # Adjust Y-axis and add value labels
        if len(df) > 0:
            max_val = df['AvgLatency'].max()
            ax1.set_ylim(0, max_val * 1.15)
        
        for i, bar in enumerate(bars1):
            height = bar.get_height()
            if height > 0:
                y_offset = max(height * 0.03, height + 5)
                ax1.text(bar.get_x() + bar.get_width()/2., y_offset,
                        f'{height:.1f}', ha='center', va='bottom', fontsize=10, fontweight='bold',
                        bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8, edgecolor='none'))
        
        # 2. Starvation Rate Comparison (Top Middle) - NEW!
        ax2 = axes[0, 1]
        bars2 = ax2.bar(range(len(df)), df['StarvationRate'], color=sns.color_palette("Reds_r", len(df)))
        ax2.set_title('Starvation Rate by Policy', fontweight='bold', fontsize=14, pad=15)
        ax2.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax2.set_ylabel('Starvation Rate (%)', fontsize=12, labelpad=10)
        ax2.set_xticks(range(len(df)))
        ax2.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax2.tick_params(axis='y', labelsize=10)
        ax2.grid(True, alpha=0.3)
        
        # Adjust Y-axis and add value labels for starvation
        if len(df) > 0:
            max_starv = df['StarvationRate'].max()
            ax2.set_ylim(0, max(max_starv * 1.15, 5))  # Ensure minimum scale
        
        for i, bar in enumerate(bars2):
            height = bar.get_height()
            if height > 0.1:
                y_offset = height + max(height * 0.05, 0.2)
                ax2.text(bar.get_x() + bar.get_width()/2., y_offset,
                        f'{height:.1f}%', ha='center', va='bottom', fontsize=10, fontweight='bold',
                        bbox=dict(boxstyle='round,pad=0.2', facecolor='red', alpha=0.7, edgecolor='darkred'))
        
        # 3. Peak Latency Comparison (Top Right)
        ax3 = axes[0, 2]
        bars3 = ax3.bar(range(len(df)), df['MaxLatency'], color=sns.color_palette("plasma", len(df)))
        ax3.set_title('Peak Latency by Policy', fontweight='bold', fontsize=14, pad=15)
        ax3.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax3.set_ylabel('Peak Latency (cycles)', fontsize=12, labelpad=10)
        ax3.set_xticks(range(len(df)))
        ax3.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax3.tick_params(axis='y', labelsize=10)
        ax3.grid(True, alpha=0.3)
        
        # Adjust Y-axis and add value labels
        if len(df) > 0:
            max_val = df['MaxLatency'].max()
            ax3.set_ylim(0, max_val * 1.12)
        
        for i, bar in enumerate(bars3):
            height = bar.get_height()
            if height > 10:
                y_offset = height + max(height * 0.02, 20)
                ax3.text(bar.get_x() + bar.get_width()/2., y_offset,
                        f'{height:.0f}', ha='center', va='bottom', fontsize=10, fontweight='bold',
                        bbox=dict(boxstyle='round,pad=0.2', facecolor='white', alpha=0.8, edgecolor='none'))
        
        # 4. QoS Compliance Rate (Bottom Left)
        ax4 = axes[1, 0]
        bars4 = ax4.bar(range(len(df)), df['QoSRate'], color=sns.color_palette("coolwarm", len(df)))
        ax4.set_title('QoS Compliance Rate by Policy', fontweight='bold', fontsize=14, pad=15)
        ax4.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax4.set_ylabel('QoS Rate (%)', fontsize=12, labelpad=10)
        ax4.set_xticks(range(len(df)))
        ax4.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax4.tick_params(axis='y', labelsize=10)
        ax4.grid(True, alpha=0.3)
        
        # Adjust Y-axis and add value labels
        if len(df) > 0:
            max_qos = df['QoSRate'].max()
            ax4.set_ylim(0, min(110, max_qos + 15))
        
        for i, bar in enumerate(bars4):
            height = bar.get_height()
            if height > 2:
                ax4.text(bar.get_x() + bar.get_width()/2., height + 2.5,
                        f'{height:.1f}%', ha='center', va='bottom', fontsize=10, fontweight='bold',
                        bbox=dict(boxstyle='round,pad=0.2', facecolor='yellow', alpha=0.7, edgecolor='orange'))
        
        # 5. Fairness Index (Bottom Middle) - NEW!
        ax5 = axes[1, 1]
        bars5 = ax5.bar(range(len(df)), df['FairnessIndex'], color=sns.color_palette("viridis_r", len(df)))
        ax5.set_title('Fairness Index by Policy', fontweight='bold', fontsize=14, pad=15)
        ax5.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
        ax5.set_ylabel('Fairness Index (1.0=Fair)', fontsize=12, labelpad=10)
        ax5.set_xticks(range(len(df)))
        ax5.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=10)
        ax5.tick_params(axis='y', labelsize=10)
        ax5.grid(True, alpha=0.3)
        ax5.set_ylim(0, 1.1)
        
        for i, bar in enumerate(bars5):
            height = bar.get_height()
            if height > 0.05:
                ax5.text(bar.get_x() + bar.get_width()/2., height + 0.03,
                        f'{height:.3f}', ha='center', va='bottom', fontsize=10, fontweight='bold',
                        bbox=dict(boxstyle='round,pad=0.2', facecolor='lightgreen', alpha=0.7, edgecolor='green'))
        
        # 6. Starvation vs Fairness Scatter Plot (Bottom Right) - NEW!
        ax6 = axes[1, 2]
        
        # Policy colors for consistency
        policy_colors = {
            'FixedPriority': '#FF6B6B',
            'RoundRobin': '#4ECDC4',  
            'Random': '#45B7D1',
            'WeightedRoundRobin': '#96CEB4',
            'DynamicPriority': '#FFA500'
        }
        
        # Plot points by policy for starvation vs fairness
        for policy_name, color in policy_colors.items():
            policy_data = df[df['PolicyPattern'].str.startswith(policy_name)]
            if not policy_data.empty:
                ax6.scatter(policy_data['StarvationRate'], policy_data['FairnessIndex'], 
                           c=color, s=120, alpha=0.8, 
                           edgecolors='black', linewidth=1.0, label=policy_name)
        
        ax6.set_title('Starvation vs Fairness Trade-off', fontweight='bold', fontsize=14, pad=15)
        ax6.set_xlabel('Starvation Rate (%)', fontsize=12, labelpad=10)
        ax6.set_ylabel('Fairness Index (1.0=Fair)', fontsize=12, labelpad=10)
        ax6.tick_params(axis='both', labelsize=10)
        ax6.grid(True, alpha=0.3)
        ax6.set_ylim(0, 1.1)
        
        # Position legend
        ax6.legend(loc='upper right', fontsize=9, framealpha=0.95, 
                  bbox_to_anchor=(0.98, 0.98), borderaxespad=0)
        
        # Add quadrant labels to help interpret the scatter plot
        ax6.text(0.02, 0.98, 'IDEAL\n(Low Starvation\nHigh Fairness)', 
                transform=ax6.transAxes, fontsize=10, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='lightgreen', alpha=0.7),
                verticalalignment='top')
        ax6.text(0.02, 0.02, 'POOR\n(Low Starvation\nLow Fairness)', 
                transform=ax6.transAxes, fontsize=10, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='yellow', alpha=0.7),
                verticalalignment='bottom')
        ax6.text(0.98, 0.98, 'ACCEPTABLE\n(High Starvation\nHigh Fairness)', 
                transform=ax6.transAxes, fontsize=10, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='orange', alpha=0.7),
                verticalalignment='top', horizontalalignment='right')
        ax6.text(0.98, 0.02, 'WORST\n(High Starvation\nLow Fairness)', 
                transform=ax6.transAxes, fontsize=10, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.3', facecolor='red', alpha=0.7),
                verticalalignment='bottom', horizontalalignment='right')
        
        
        # Save combined plot
        plot_filename = f"performance_analysis_{traffic_mix}.png"
        plot_path = os.path.join(script_dir, plot_filename)
        plt.savefig(plot_path, dpi=300, bbox_inches='tight', facecolor='white', edgecolor='none')
        print(f"  Saved: {plot_filename}")
        
        plt.close()
    
    print(f"\nAll combined plots generated successfully!")
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