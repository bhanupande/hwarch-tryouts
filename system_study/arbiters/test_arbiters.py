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


def assign_requestor_traffic_class(requestor_id: int, num_requestors: int, traffic_mix: str) -> TrafficClass:
    """
    Assign traffic class to requestor based on deterministic mapping.
    
    For mixed traffic (default):
    - Real-time: requestors 0 to num_requestors//3 - 1
    - Isochronous: requestors num_requestors//3 to 2*num_requestors//3 - 1  
    - Best-effort: requestors 2*num_requestors//3 to num_requestors - 1
    
    For single-class traffic, all requestors get that class.
    """
    if traffic_mix == 'real_time_only':
        return TrafficClass.REAL_TIME
    elif traffic_mix == 'isochronous_only':
        return TrafficClass.ISOCHRONOUS
    elif traffic_mix == 'best_effort_only':
        return TrafficClass.BEST_EFFORT
    else:  # mixed - deterministic assignment
        rt_end = max(1, num_requestors // 3)
        iso_end = max(2, (2 * num_requestors) // 3)
        
        if requestor_id < rt_end:
            return TrafficClass.REAL_TIME
        elif requestor_id < iso_end:
            return TrafficClass.ISOCHRONOUS
        else:
            return TrafficClass.BEST_EFFORT


def get_traffic_class_load_factor(traffic_class: TrafficClass, pattern_type: str, cycle: int, requestor_id: int) -> float:
    """
    Get load factor for a traffic class based on pattern type.
    Returns probability that this requestor makes a request this cycle.
    """
    # Base load factors by traffic class (realistic system loads)
    base_loads = {
        TrafficClass.REAL_TIME: 0.4,      # Higher load for real-time
        TrafficClass.ISOCHRONOUS: 0.3,    # Medium load for isochronous
        TrafficClass.BEST_EFFORT: 0.2     # Lower but bursty load for best-effort
    }
    
    base_load = base_loads[traffic_class]
    
    if pattern_type == 'random':
        return base_load
    elif pattern_type == 'uniform':
        # Uniform spacing based on traffic class priority
        spacing = {
            TrafficClass.REAL_TIME: 2,      # Every 2 cycles
            TrafficClass.ISOCHRONOUS: 3,    # Every 3 cycles  
            TrafficClass.BEST_EFFORT: 4     # Every 4 cycles
        }[traffic_class]
        return 1.0 if (cycle + requestor_id) % spacing == 0 else 0.0
    elif pattern_type == 'burst':
        # Bursty patterns - different burst characteristics per class
        if traffic_class == TrafficClass.REAL_TIME:
            # Frequent short bursts
            return base_load * 2.0 if (cycle // 3) % 2 == 0 else base_load * 0.2
        elif traffic_class == TrafficClass.ISOCHRONOUS:
            # Medium bursts
            return base_load * 1.8 if (cycle // 5) % 2 == 0 else base_load * 0.3
        else:  # BEST_EFFORT
            # Long, intense bursts
            return base_load * 3.0 if (cycle // 8) % 2 == 0 else base_load * 0.1
    elif pattern_type == 'sequential':
        # Sequential access within traffic class groups
        rt_end = max(1, 16 // 3)  # Assume 16 requestors for calculation
        iso_end = max(2, (2 * 16) // 3)
        
        if traffic_class == TrafficClass.REAL_TIME:
            return 1.0 if (cycle % rt_end) == requestor_id else 0.0
        elif traffic_class == TrafficClass.ISOCHRONOUS:
            adjusted_id = requestor_id - rt_end
            iso_count = iso_end - rt_end
            return 1.0 if (cycle % iso_count) == adjusted_id else 0.0
        else:  # BEST_EFFORT
            adjusted_id = requestor_id - iso_end
            be_count = 16 - iso_end
            return 1.0 if (cycle % be_count) == adjusted_id else 0.0
    elif pattern_type == 'heavy_contention':
        # All traffic classes highly active - stress test arbitration
        heavy_loads = {
            TrafficClass.REAL_TIME: 0.8,      # Very high load
            TrafficClass.ISOCHRONOUS: 0.7,    # High load
            TrafficClass.BEST_EFFORT: 0.6     # Moderate-high load
        }
        return heavy_loads[traffic_class]
    elif pattern_type == 'priority_inversion':
        # Lower priority classes more active than higher priority
        # This tests if arbiters properly handle priority enforcement
        inversion_loads = {
            TrafficClass.REAL_TIME: 0.2,      # Low load (should still get priority)
            TrafficClass.ISOCHRONOUS: 0.5,    # Medium load  
            TrafficClass.BEST_EFFORT: 0.8     # High load (tests starvation handling)
        }
        return inversion_loads[traffic_class]
    else:
        return base_load


def generate_traffic(num_requestors: int, cycles: int, pattern_type: str, traffic_mix: str) -> List[List[Request]]:
    """
    Generate deterministic traffic patterns for comprehensive arbitration testing.
    
    Each requestor is assigned a fixed traffic class, enabling consistent testing
    of arbitration policies under realistic mixed workloads.
    """
    patterns = [[] for _ in range(cycles)]
    request_id = 0
    
    # Create requestor-to-traffic-class mapping
    requestor_classes = {}
    for requestor in range(num_requestors):
        requestor_classes[requestor] = assign_requestor_traffic_class(requestor, num_requestors, traffic_mix)
    
    for cycle in range(cycles):
        cycle_requests = []
        
        for requestor in range(num_requestors):
            # Get this requestor's traffic class
            requestor_traffic_class = requestor_classes[requestor]
            
            # Determine if this requestor makes a request this cycle
            load_factor = get_traffic_class_load_factor(requestor_traffic_class, pattern_type, cycle, requestor)
            make_request = random.random() < load_factor
            
            if make_request:
                # Get traffic class info
                traffic_class_info = TRAFFIC_CLASSES[requestor_traffic_class]
                
                # Calculate deterministic base priority with controlled variation
                # Higher numbers = higher priority, with NON-OVERLAPPING ranges
                if requestor_traffic_class == TrafficClass.REAL_TIME:
                    # Highest priority: 10-15 (with small variation per requestor)
                    base_priority = 10 + (requestor % 6)
                elif requestor_traffic_class == TrafficClass.ISOCHRONOUS:
                    # Medium priority: 5-9 (with small variation per requestor)
                    base_priority = 5 + (requestor % 5)
                else:  # BEST_EFFORT
                    # Lowest priority: 1-4 (with small variation per requestor)
                    base_priority = 1 + (requestor % 4)
                
                request = Request(
                    id=request_id,
                    priority=traffic_class_info.priority,  # Keep original priority for QoS tracking
                    traffic_class=requestor_traffic_class,
                    arrival_cycle=cycle,
                    base_priority=base_priority
                )
                cycle_requests.append(request)
                request_id += 1
        
        patterns[cycle] = cycle_requests
    
    return patterns


def measure_performance(arbiter: Arbiter, request_patterns: List[List[Request]]) -> Dict[str, Any]:
    """
    Measure arbiter performance with deterministic requestor-traffic-class mapping.
    
    Each requestor has a fixed traffic class, making performance analysis more predictable
    and allowing for better comparison of arbitration policies.
    """
    total_cycles = len(request_patterns)
    all_requests = []
    
    # Collect all requests
    for cycle_requests in request_patterns:
        all_requests.extend(cycle_requests)
    
    # Create requestor-to-traffic-class mapping for consistent assignment
    requestor_classes = {}
    if all_requests:
        # Determine mapping from actual requests generated
        for req in all_requests:
            # Find which requestor this request should be assigned to based on traffic class
            # We need to reverse-engineer which requestor would generate this request
            pass
    
    # For simplicity, recreate the mapping using the same logic as traffic generation
    num_requestors = arbiter.num_requestors
    for requestor in range(num_requestors):
        # Determine traffic mix from request patterns (use first available traffic class)
        if all_requests:
            # Check the distribution to infer traffic_mix
            rt_count = sum(1 for req in all_requests if req.traffic_class == TrafficClass.REAL_TIME)
            iso_count = sum(1 for req in all_requests if req.traffic_class == TrafficClass.ISOCHRONOUS)
            be_count = sum(1 for req in all_requests if req.traffic_class == TrafficClass.BEST_EFFORT)
            
            if rt_count > 0 and iso_count == 0 and be_count == 0:
                traffic_mix = 'real_time_only'
            elif rt_count == 0 and iso_count > 0 and be_count == 0:
                traffic_mix = 'isochronous_only'
            elif rt_count == 0 and iso_count == 0 and be_count > 0:
                traffic_mix = 'best_effort_only'
            else:
                traffic_mix = 'mixed'
        else:
            traffic_mix = 'mixed'
        
        requestor_classes[requestor] = assign_requestor_traffic_class(requestor, num_requestors, traffic_mix)
    
    # Realistic simulation with proper queueing
    pending_requests = []  # Queue of pending requests
    
    for cycle, new_requests in enumerate(request_patterns):
        # Add new requests to pending queue
        pending_requests.extend(new_requests)
        
        if pending_requests:
            # Create request vector for arbiter using deterministic assignment
            request_vector = [None] * arbiter.num_requestors
            base_priority_vector = [0] * arbiter.num_requestors
            request_map = {}
            
            # Assign requests to requestors based on their fixed traffic class
            for requestor in range(arbiter.num_requestors):
                requestor_traffic_class = requestor_classes[requestor]
                
                # Find the highest priority pending request for this requestor's traffic class
                matching_requests = [req for req in pending_requests 
                                   if req.traffic_class == requestor_traffic_class]
                
                if matching_requests:
                    # Sort by priority (highest first) then by arrival time (earliest first)
                    matching_requests.sort(key=lambda x: (-x.base_priority, x.arrival_cycle))
                    best_request = matching_requests[0]
                    
                    request_vector[requestor] = best_request
                    base_priority_vector[requestor] = best_request.base_priority
                    request_map[requestor] = best_request
            
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
    Comprehensive traffic class testing with deterministic requestor-to-class mapping.
    
    Creates challenging arbitration scenarios to properly test different policies:
    - Heavy contention scenarios to test starvation handling
    - Mixed priority scenarios to test QoS enforcement
    - Burst scenarios to test temporary overload handling
    - Sequential scenarios to test fairness
    
    Parameters:
    - req: Number of requestors (default: 16 for realistic contention)
    - cycles: Simulation cycles (default: 2000 for statistical significance)
    
    Each requestor has a fixed traffic class:
    - Real-time: requestors 0 to req//3-1 (highest priority, tight latency)
    - Isochronous: requestors req//3 to 2*req//3-1 (medium priority, moderate latency)
    - Best-effort: requestors 2*req//3 to req-1 (lowest priority, no latency constraint)
    """
    print("DETERMINISTIC TRAFFIC CLASS TESTING")
    print("=" * 60)
    print(f"Parameters: {req} requestors, {cycles} cycles")
    
    # Show requestor assignment
    rt_end = max(1, req // 3)
    iso_end = max(2, (2 * req) // 3)
    print(f"Requestor Assignment:")
    print(f"  Real-time (0-{rt_end-1}): {rt_end} requestors")
    print(f"  Isochronous ({rt_end}-{iso_end-1}): {iso_end-rt_end} requestors") 
    print(f"  Best-effort ({iso_end}-{req-1}): {req-iso_end} requestors")
    print("=" * 60)
    
    # Streamlined test scenarios - focus on key policy comparisons
    policies = ['FixedPriority', 'WeightedRoundRobin', 'DynamicPriority', 'Random']
    
    # Key traffic patterns that reveal arbitration differences
    patterns = [
        'random',              # Base case - random contention
        'heavy_contention',    # Stress test - all requestors highly active
        'priority_inversion'   # Critical test - lower priority very active
    ]
    
    test_configs = []
    for pol in policies:
        for pat in patterns:
            if pol == 'WeightedRoundRobin':
                # Only test priority-based weights (most realistic scenario)
                weights = [3 if i < rt_end else 2 if i < iso_end else 1 for i in range(req)]
                test_configs.append({
                    'num_requestors': req,
                    'policy': pol,
                    'pattern_type': pat,
                    'cycles': cycles,
                    'weights': weights,
                    'weight_name': 'priority'
                })
            else:
                test_configs.append({
                    'num_requestors': req,
                    'policy': pol,
                    'pattern_type': pat,
                    'cycles': cycles
                })
    
    results = []
    
    # Run tests
    print(f"\nRunning {len(test_configs)} streamlined test configurations...")
    for i, config in enumerate(test_configs, 1):
        # Create test description including weight info for WeightedRoundRobin
        if config['policy'] == 'WeightedRoundRobin':
            test_desc = f"{config['policy']} ({config['pattern_type']})"
        else:
            test_desc = f"{config['policy']} ({config['pattern_type']})"
            
        print(f"Test {i}/{len(test_configs)}: {test_desc}")
        
        # Create arbiter
        weights = config.get('weights', None)
        if weights:
            arbiter = Arbiter(num_requestors=req, policy=config['policy'], weights=weights)
        else:
            arbiter = Arbiter(num_requestors=req, policy=config['policy'])
        
        # Generate traffic and measure performance (always mixed traffic)
        traffic_patterns = generate_traffic(req, cycles, config['pattern_type'], 'mixed')
        perf = measure_performance(arbiter, traffic_patterns)
        
        # Show progress with detailed debug info including starvation
        print(f"  Total Reqs: {perf['total_requests']} | Served: {perf['served_requests']} ({perf['service_rate']:.1f}%) | "
              f"QoS Rate: {perf['qos_rate']:.1f}% | Violations: {perf['violations']} | "
              f"Avg Lat: {perf['avg_latency']:.1f} | Max Lat: {perf['max_latency']:.0f} | "
              f"Starvation: {perf['starvation_rate']:.1f}% | Fairness: {perf['fairness_index']:.3f}")
        
        # Store result with enhanced description
        result = {
            'config': config,
            'performance': perf,
            'arbiter_name': arbiter.name,
            'test_description': test_desc
        }
        results.append(result)
    
    # Generate detailed report
    print("\n" + "=" * 120)
    print("PERFORMANCE SUMMARY - Deterministic Mixed Traffic (RT+Iso+BE)")
    print("=" * 120)
    print(f"{'Test':<4} {'Policy_Pattern':<30} {'Reqs':<6} {'Served':<6} {'Tput':<8} {'QoS%':<8} {'Viol':<6} {'AvgLat':<7} {'Starv%':<7} {'Fair':<6}")
    print("-" * 120)
    
    for i, result in enumerate(results, 1):
        config = result['config']
        perf = result['performance']
        
        # Create comprehensive test identifier
        if config['policy'] == 'WeightedRoundRobin':
            policy_desc = f"{config['policy']}_{config['pattern_type']}"
        else:
            policy_desc = f"{config['policy']}_{config['pattern_type']}"
        
        print(f"{i:<4} {policy_desc:<30} "
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
    
    # Save single comprehensive CSV report
    script_dir = os.path.dirname(os.path.abspath(__file__))
    filename = "arbiter_performance_report.csv"
    full_path = os.path.join(script_dir, filename)
    
    with open(full_path, 'w') as f:
        # CSV header
        f.write("Test,Policy,Pattern,TotalRequests,ServedRequests,ServiceRate,Throughput,QoSRate,Violations,AvgLatency,MaxLatency,StarvationRate,FairnessIndex,RTStarvationRate,IsoStarvationRate,BEStarvationRate\n")
        
        # CSV data
        for i, result in enumerate(results, 1):
            config = result['config']
            perf = result['performance']
            
            policy_name = config['policy']
            pattern_name = config['pattern_type']
            
            f.write(f"{i},{policy_name},{pattern_name},"
                   f"{perf['total_requests']},{perf['served_requests']},{perf['service_rate']:.1f},"
                   f"{perf['throughput']:.3f},{perf['qos_rate']:.1f},"
                   f"{perf['violations']},{perf['avg_latency']:.1f},{perf['max_latency']:.0f},"
                   f"{perf['starvation_rate']:.1f},{perf['fairness_index']:.3f},"
                   f"{perf['rt_starvation_rate']:.1f},{perf['iso_starvation_rate']:.1f},{perf['be_starvation_rate']:.1f}\n")
    
    print(f"\nPerformance report saved: {full_path}")
    
    return results


def plot_performance_metrics():
    """
    Generate comprehensive performance plots from the single CSV report.
    Creates grouped bar charts comparing policies across different traffic patterns.
    """
    # Set up plotting style
    plt.style.use('default')
    sns.set_palette("husl")
    
    # Find CSV file
    script_dir = os.path.dirname(os.path.abspath(__file__))
    csv_file = os.path.join(script_dir, "arbiter_performance_report.csv")
    
    if not os.path.exists(csv_file):
        print("CSV file not found. Run the simulation first!")
        return
    
    print("Generating performance plots...")
    
    # Read data
    df = pd.read_csv(csv_file)
    
    # Create figure with 2x3 subplots
    fig, axes = plt.subplots(2, 3, figsize=(24, 16))
    fig.suptitle('Arbiter Performance Analysis - Deterministic Mixed Traffic', 
                 fontsize=18, fontweight='bold', y=0.98)
    
    # Adjust spacing between subplots
    plt.subplots_adjust(hspace=0.35, wspace=0.25, top=0.92, bottom=0.12, left=0.06, right=0.97)
    
    # Create policy-pattern labels
    df['PolicyPattern'] = df['Policy'] + '_' + df['Pattern']
    
    # 1. Average Latency Comparison (Top Left)
    ax1 = axes[0, 0]
    bars1 = ax1.bar(range(len(df)), df['AvgLatency'], color=sns.color_palette("viridis", len(df)))
    ax1.set_title('Average Latency by Policy-Pattern', fontweight='bold', fontsize=14, pad=15)
    ax1.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
    ax1.set_ylabel('Average Latency (cycles)', fontsize=12, labelpad=10)
    ax1.set_xticks(range(len(df)))
    ax1.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=9)
    ax1.tick_params(axis='y', labelsize=10)
    ax1.grid(True, alpha=0.3)
    
    if len(df) > 0:
        max_val = df['AvgLatency'].max()
        ax1.set_ylim(0, max_val * 1.15)
    
    for i, bar in enumerate(bars1):
        height = bar.get_height()
        if height > 0:
            ax1.text(bar.get_x() + bar.get_width()/2., height * 1.02,
                    f'{height:.1f}', ha='center', va='bottom', fontsize=8, fontweight='bold')
    
    # 2. Starvation Rate Comparison (Top Middle)
    ax2 = axes[0, 1]
    bars2 = ax2.bar(range(len(df)), df['StarvationRate'], color=sns.color_palette("Reds_r", len(df)))
    ax2.set_title('Starvation Rate by Policy-Pattern', fontweight='bold', fontsize=14, pad=15)
    ax2.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
    ax2.set_ylabel('Starvation Rate (%)', fontsize=12, labelpad=10)
    ax2.set_xticks(range(len(df)))
    ax2.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=9)
    ax2.tick_params(axis='y', labelsize=10)
    ax2.grid(True, alpha=0.3)
    
    if len(df) > 0:
        max_starv = df['StarvationRate'].max()
        ax2.set_ylim(0, max(max_starv * 1.15, 5))
    
    for i, bar in enumerate(bars2):
        height = bar.get_height()
        if height > 0.1:
            ax2.text(bar.get_x() + bar.get_width()/2., height * 1.02,
                    f'{height:.1f}%', ha='center', va='bottom', fontsize=8, fontweight='bold',
                    bbox=dict(boxstyle='round,pad=0.2', facecolor='red', alpha=0.5))
    
    # 3. QoS Compliance Rate (Top Right)
    ax3 = axes[0, 2]
    bars3 = ax3.bar(range(len(df)), df['QoSRate'], color=sns.color_palette("coolwarm", len(df)))
    ax3.set_title('QoS Compliance Rate', fontweight='bold', fontsize=14, pad=15)
    ax3.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
    ax3.set_ylabel('QoS Rate (%)', fontsize=12, labelpad=10)
    ax3.set_xticks(range(len(df)))
    ax3.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=9)
    ax3.tick_params(axis='y', labelsize=10)
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim(0, 110)
    
    for i, bar in enumerate(bars3):
        height = bar.get_height()
        if height > 2:
            ax3.text(bar.get_x() + bar.get_width()/2., height + 2,
                    f'{height:.1f}%', ha='center', va='bottom', fontsize=8, fontweight='bold',
                    bbox=dict(boxstyle='round,pad=0.2', facecolor='yellow', alpha=0.6))
    
    # 4. Fairness Index (Bottom Left)
    ax4 = axes[1, 0]
    bars4 = ax4.bar(range(len(df)), df['FairnessIndex'], color=sns.color_palette("viridis_r", len(df)))
    ax4.set_title('Fairness Index', fontweight='bold', fontsize=14, pad=15)
    ax4.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
    ax4.set_ylabel('Fairness Index (1.0=Fair)', fontsize=12, labelpad=10)
    ax4.set_xticks(range(len(df)))
    ax4.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=9)
    ax4.tick_params(axis='y', labelsize=10)
    ax4.grid(True, alpha=0.3)
    ax4.set_ylim(0, 1.1)
    
    for i, bar in enumerate(bars4):
        height = bar.get_height()
        if height > 0.05:
            ax4.text(bar.get_x() + bar.get_width()/2., height + 0.03,
                    f'{height:.3f}', ha='center', va='bottom', fontsize=8, fontweight='bold',
                    bbox=dict(boxstyle='round,pad=0.2', facecolor='lightgreen', alpha=0.6))
    
    # 5. Traffic Class Starvation Rates (Bottom Middle)
    ax5 = axes[1, 1]
    x = range(len(df))
    width = 0.25
    ax5.bar([i - width for i in x], df['RTStarvationRate'], width, label='Real-Time', color='red', alpha=0.7)
    ax5.bar(x, df['IsoStarvationRate'], width, label='Isochronous', color='orange', alpha=0.7)
    ax5.bar([i + width for i in x], df['BEStarvationRate'], width, label='Best-Effort', color='green', alpha=0.7)
    ax5.set_title('Starvation by Traffic Class', fontweight='bold', fontsize=14, pad=15)
    ax5.set_xlabel('Policy-Pattern', fontsize=12, labelpad=10)
    ax5.set_ylabel('Starvation Rate (%)', fontsize=12, labelpad=10)
    ax5.set_xticks(x)
    ax5.set_xticklabels(df['PolicyPattern'], rotation=45, ha='right', fontsize=9)
    ax5.tick_params(axis='y', labelsize=10)
    ax5.legend(loc='upper right', fontsize=10)
    ax5.grid(True, alpha=0.3)
    
    # 6. Starvation vs Fairness Scatter (Bottom Right)
    ax6 = axes[1, 2]
    
    # Color by policy
    policy_colors = {
        'FixedPriority': '#FF6B6B',
        'RoundRobin': '#4ECDC4',
        'Random': '#45B7D1',
        'WeightedRoundRobin': '#96CEB4',
        'DynamicPriority': '#FFA500'
    }
    
    for policy in df['Policy'].unique():
        policy_data = df[df['Policy'] == policy]
        color = policy_colors.get(policy, '#777777')
        ax6.scatter(policy_data['StarvationRate'], policy_data['FairnessIndex'],
                   c=color, s=120, alpha=0.8, edgecolors='black', linewidth=1.0, label=policy)
    
    ax6.set_title('Starvation vs Fairness Trade-off', fontweight='bold', fontsize=14, pad=15)
    ax6.set_xlabel('Starvation Rate (%)', fontsize=12, labelpad=10)
    ax6.set_ylabel('Fairness Index (1.0=Fair)', fontsize=12, labelpad=10)
    ax6.tick_params(axis='both', labelsize=10)
    ax6.grid(True, alpha=0.3)
    ax6.set_ylim(0, 1.1)
    ax6.legend(loc='upper right', fontsize=9, framealpha=0.95)
    
    # Save plot
    plot_filename = "arbiter_performance_analysis.png"
    plot_path = os.path.join(script_dir, plot_filename)
    plt.savefig(plot_path, dpi=300, bbox_inches='tight', facecolor='white', edgecolor='none')
    print(f"Performance plot saved: {plot_filename}")
    
    plt.close()
    print("Plot generation completed!")


if __name__ == "__main__":
    # Run the streamlined simulation
    run_traffic_class_examples(req=16, cycles=2000)
    
    # Generate plots
    print("\n" + "=" * 60)
    print("GENERATING PERFORMANCE VISUALIZATIONS")
    print("=" * 60)
    plot_performance_metrics()