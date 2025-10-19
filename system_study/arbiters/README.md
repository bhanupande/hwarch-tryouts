# Arbiter Performance Testing Framework

This testing framework evaluates the performance of different arbiter configurations and provides comprehensive reports with key performance metrics.

## Files

- `arbiters.py` - Main Arbiter class implementation
- `test_arbiters.py` - Comprehensive testing framework with integrated examples
- `README.md` - This documentation

## Quick Start

### Run Full Test Suite
```bash
python test_arbiters.py
```
This will run a comprehensive test suite with multiple configurations and generate a detailed performance report.

### Run Example Scenarios
```bash
python test_arbiters.py --examples
```
This demonstrates various testing scenarios including custom configurations, policy comparisons, and stress tests.

### Get Help
```bash
python test_arbiters.py --help
```
Shows usage information and available options.

## Performance Metrics

The testing framework measures three key performance indicators:

### 1. Throughput
- **Definition**: Number of requests processed per cycle
- **Formula**: `total_requests_served / total_cycles`
- **Range**: 0.0 to 1.0 (for single output arbiters)
- **Higher is better**

### 2. Latency
- **Definition**: Average number of cycles a request waits before being granted
- **Measured**: From when request arrives until it's granted
- **Assumption**: No request loss - requestors wait until granted
- **Lower is better**

### 3. Utilization
- **Definition**: Percentage of time the arbiter is actively processing requests
- **Formula**: `active_cycles / total_cycles * 100%`
- **Range**: 0% to 100%
- **Higher is better**

## Arbiter Configurations

### Policies Supported
- **FixedPriority**: Always grants to lowest-numbered active requestor
- **RoundRobin**: Cycles through requestors in order
- **Random**: Randomly selects among active requestors

### Traffic Patterns
- **Random**: 50% probability per requestor per cycle
- **Burst**: Alternating high/low activity periods
- **Sequential**: One requestor active per cycle in sequence
- **Uniform**: All requestors active every cycle

## Usage Examples

### Basic Usage
```python
from test_arbiters import ArbitratorTester

# Create tester
tester = ArbitratorTester()

# Define configuration
config = {
    'num_requestors': 4,
    'num_outputs': 1,
    'policy': 'RoundRobin',
    'pattern_type': 'random',
    'cycles': 1000
}

# Run test
result = tester.run_test_configuration(config)

# Access results
print(f"Throughput: {result['throughput']:.3f}")
print(f"Latency: {result['avg_latency']:.2f}")
print(f"Utilization: {result['utilization']:.2%}")
```

### Run Built-in Examples
```bash
# Run all example scenarios
python test_arbiters.py --examples

# Includes:
# 1. Custom configuration example
# 2. Policy comparison
# 3. Stress testing scenarios
```

### Custom Test Suite (Programmatic)
```python
# Run multiple configurations
configs = [
    {'num_requestors': 4, 'policy': 'FixedPriority', 'pattern_type': 'random', 'cycles': 1000},
    {'num_requestors': 4, 'policy': 'RoundRobin', 'pattern_type': 'random', 'cycles': 1000},
    {'num_requestors': 8, 'policy': 'FixedPriority', 'pattern_type': 'uniform', 'cycles': 1000},
]

results = []
for config in configs:
    result = tester.run_test_configuration(config)
    results.append(result)

# Generate report
report = tester.generate_report(results)
print(report)
```

## Report Format

The generated reports include:

1. **Performance Summary Table**: Quick overview of all test configurations
2. **Detailed Results**: Comprehensive metrics for each test
3. **Performance Analysis**: Best performers and policy comparisons
4. **Policy Comparison**: Average performance by arbitration policy

Reports are automatically saved to timestamped files (e.g., `arbiter_report_20231019_152819.txt`).

## Key Insights from Testing

### FixedPriority Policy
- **Advantages**: 
  - Low latency for high-priority requestors
  - Simple implementation
  - Predictable behavior
- **Disadvantages**:
  - Potential starvation of low-priority requestors
  - Unfair resource allocation

### RoundRobin Policy
- **Advantages**:
  - Fair resource allocation
  - No starvation
  - Good for uniform traffic
- **Disadvantages**:
  - Higher average latency with many requestors
  - Less efficient for priority-based systems

### Random Policy
- **Advantages**:
  - Simple implementation
  - Fair over time
- **Disadvantages**:
  - Unpredictable behavior
  - May not be suitable for real-time systems

## Advanced Features

### Stress Testing
Test with high numbers of requestors (32, 64+) to evaluate scalability:

```python
stress_config = {
    'num_requestors': 32,
    'num_outputs': 1,
    'policy': 'RoundRobin',
    'pattern_type': 'uniform',
    'cycles': 2000
}
```

### Pattern Analysis
Compare how different traffic patterns affect performance:

- **Sequential**: Best for round-robin (perfect match)
- **Uniform**: Stresses the arbiter maximally
- **Burst**: Simulates real-world bursty traffic
- **Random**: General-purpose testing pattern

## Extending the Framework

### Adding New Policies
1. Implement policy in `arbiters.py` `arb_policy()` method
2. Add policy name to supported list in tests
3. Test with various configurations

### Adding New Metrics
1. Modify `simulate_arbitration()` to collect new data
2. Update report generation to include new metrics
3. Add analysis functions for the new metrics

### Custom Traffic Patterns
Add new patterns to `generate_request_pattern()` method:

```python
elif pattern_type == 'custom':
    # Your custom pattern logic here
    for cycle in range(cycles):
        pattern = your_custom_logic(cycle, num_requestors)
        patterns.append(pattern)
```