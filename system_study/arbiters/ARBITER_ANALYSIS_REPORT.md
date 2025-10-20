# Arbiter Performance Analysis Report

**Generated:** 2025-10-20 16:37:25

---

## 📊 Test Configuration

- **Requestors:** 16 (5 Real-time, 5 Isochronous, 6 Best-effort)
- **Simulation Cycles:** 2000
- **Traffic Patterns:** random, heavy_contention, priority_inversion
- **Arbiter Policies:** FixedPriority, WeightedRoundRobin, DynamicPriority, Random

### Traffic Class Assignment

| Requestor Range | Traffic Class | Priority | Max Latency Constraint |
|----------------|---------------|----------|------------------------|
| 0-4            | Real-time     | Highest  | 10 cycles              |
| 5-9            | Isochronous   | Medium   | 20 cycles              |
| 10-15          | Best-effort   | Lowest   | None                   |

---

## 🔍 Key Findings by Arbitration Policy

### 🏷️ FixedPriority Arbiter

#### 📈 Overall Performance

- **Average QoS Compliance:** 77.6%
- **Average Starvation Rate:** 89.9%
- **Average Fairness Index:** 0.366
- **Average Latency:** 95.9 cycles
- **Average QoS Violations:** 447 requests

#### 📋 Performance by Traffic Pattern

**RANDOM**

- Requests Generated: 15,636
- Requests Served: 2,000 (12.8%)
- QoS Compliance: 61.2%
- QoS Violations: 777
- Average Latency: 127.9 cycles
- Maximum Latency: 625 cycles
- Overall Starvation: 87.2%
- Fairness Index: 0.366
- RT Starvation: 66.4%
- Iso Starvation: 100.0%
- BE Starvation: 100.0%

**HEAVY_CONTENTION**

- Requests Generated: 26,524
- Requests Served: 2,000 (7.5%)
- QoS Compliance: 90.5%
- QoS Violations: 189
- Average Latency: 88.0 cycles
- Maximum Latency: 1783 cycles
- Overall Starvation: 92.5%
- Fairness Index: 0.366
- RT Starvation: 77.7%
- Iso Starvation: 100.0%
- BE Starvation: 100.0%

**PRIORITY_INVERSION**

- Requests Generated: 19,775
- Requests Served: 2,000 (10.1%)
- QoS Compliance: 81.2%
- QoS Violations: 375
- Average Latency: 71.9 cycles
- Maximum Latency: 1382 cycles
- Overall Starvation: 89.9%
- Fairness Index: 0.366
- RT Starvation: 33.5%
- Iso Starvation: 100.0%
- BE Starvation: 100.0%

#### 💡 Key Insights

- ✅ **Excellent QoS compliance** (77.6%) - reliably meets latency constraints
- ✅ **Low latency** for high-priority traffic
- ⚠️ **High starvation rate** (89.9%) - low-priority traffic suffers
- ⚠️ **Poor fairness** (0.366) - heavily favors real-time traffic
- 📌 **Best for:** Systems where QoS guarantees are critical

### 🏷️ WeightedRoundRobin Arbiter

#### 📈 Overall Performance

- **Average QoS Compliance:** 29.5%
- **Average Starvation Rate:** 89.9%
- **Average Fairness Index:** 0.690
- **Average Latency:** 443.4 cycles
- **Average QoS Violations:** 1410 requests

#### 📋 Performance by Traffic Pattern

**RANDOM**

- Requests Generated: 15,869
- Requests Served: 2,000 (12.6%)
- QoS Compliance: 21.1%
- QoS Violations: 1579
- Average Latency: 361.1 cycles
- Maximum Latency: 1485 cycles
- Overall Starvation: 87.4%
- Fairness Index: 0.696
- RT Starvation: 83.9%
- Iso Starvation: 87.3%
- BE Starvation: 91.9%

**HEAVY_CONTENTION**

- Requests Generated: 26,443
- Requests Served: 2,000 (7.6%)
- QoS Compliance: 20.0%
- QoS Violations: 1600
- Average Latency: 588.7 cycles
- Maximum Latency: 1742 cycles
- Overall Starvation: 92.4%
- Fairness Index: 0.687
- RT Starvation: 89.0%
- Iso Starvation: 92.6%
- BE Starvation: 95.7%

**PRIORITY_INVERSION**

- Requests Generated: 19,763
- Requests Served: 2,000 (10.1%)
- QoS Compliance: 47.4%
- QoS Violations: 1051
- Average Latency: 380.4 cycles
- Maximum Latency: 1792 cycles
- Overall Starvation: 89.9%
- Fairness Index: 0.686
- RT Starvation: 67.6%
- Iso Starvation: 89.0%
- BE Starvation: 96.6%

#### 💡 Key Insights

- ✅ **Good fairness** (0.690) - balanced service across traffic classes
- ✅ **Moderate QoS compliance** (29.5%)
- ⚠️ **Higher average latency** (443.4 cycles) due to round-robin scheduling
- 📌 **Best for:** Systems requiring fairness with some QoS awareness

### 🏷️ DynamicPriority Arbiter

#### 📈 Overall Performance

- **Average QoS Compliance:** 38.0%
- **Average Starvation Rate:** 89.9%
- **Average Fairness Index:** 0.781
- **Average Latency:** 499.0 cycles
- **Average QoS Violations:** 1241 requests

#### 📋 Performance by Traffic Pattern

**RANDOM**

- Requests Generated: 15,806
- Requests Served: 2,000 (12.7%)
- QoS Compliance: 27.8%
- QoS Violations: 1445
- Average Latency: 421.9 cycles
- Maximum Latency: 1352 cycles
- Overall Starvation: 87.3%
- Fairness Index: 0.776
- RT Starvation: 85.2%
- Iso Starvation: 88.2%
- BE Starvation: 89.2%

**HEAVY_CONTENTION**

- Requests Generated: 26,476
- Requests Served: 2,000 (7.6%)
- QoS Compliance: 27.5%
- QoS Violations: 1451
- Average Latency: 631.0 cycles
- Maximum Latency: 1629 cycles
- Overall Starvation: 92.4%
- Fairness Index: 0.776
- RT Starvation: 90.2%
- Iso Starvation: 93.1%
- BE Starvation: 94.1%

**PRIORITY_INVERSION**

- Requests Generated: 19,837
- Requests Served: 2,000 (10.1%)
- QoS Compliance: 58.7%
- QoS Violations: 827
- Average Latency: 444.0 cycles
- Maximum Latency: 1705 cycles
- Overall Starvation: 89.9%
- Fairness Index: 0.792
- RT Starvation: 71.9%
- Iso Starvation: 90.0%
- BE Starvation: 95.0%

#### 💡 Key Insights

- ✅ **Balanced approach** - 38.0% QoS, 0.781 fairness
- ✅ **Adapts to traffic conditions** through priority aging
- 📌 **Best for:** General-purpose systems with mixed workloads

### 🏷️ Random Arbiter

#### 📈 Overall Performance

- **Average QoS Compliance:** 77.7%
- **Average Starvation Rate:** 89.9%
- **Average Fairness Index:** 0.366
- **Average Latency:** 99.1 cycles
- **Average QoS Violations:** 447 requests

#### 📋 Performance by Traffic Pattern

**RANDOM**

- Requests Generated: 15,886
- Requests Served: 2,000 (12.6%)
- QoS Compliance: 60.2%
- QoS Violations: 796
- Average Latency: 134.7 cycles
- Maximum Latency: 624 cycles
- Overall Starvation: 87.4%
- Fairness Index: 0.366
- RT Starvation: 66.9%
- Iso Starvation: 100.0%
- BE Starvation: 100.0%

**HEAVY_CONTENTION**

- Requests Generated: 26,478
- Requests Served: 2,000 (7.6%)
- QoS Compliance: 89.0%
- QoS Violations: 219
- Average Latency: 98.2 cycles
- Maximum Latency: 1750 cycles
- Overall Starvation: 92.4%
- Fairness Index: 0.366
- RT Starvation: 77.7%
- Iso Starvation: 100.0%
- BE Starvation: 100.0%

**PRIORITY_INVERSION**

- Requests Generated: 19,798
- Requests Served: 2,000 (10.1%)
- QoS Compliance: 83.8%
- QoS Violations: 325
- Average Latency: 64.3 cycles
- Maximum Latency: 1228 cycles
- Overall Starvation: 89.9%
- Fairness Index: 0.366
- RT Starvation: 33.4%
- Iso Starvation: 100.0%
- BE Starvation: 100.0%

#### 💡 Key Insights

- ✅ **Simple implementation** with no state tracking
- ⚠️ **High starvation** (89.9%) - unpredictable service
- ⚠️ **Poor fairness** (0.366) - uneven service distribution
- ⚠️ **No QoS awareness** - not suitable for real-time systems
- 📌 **Best for:** Testing baseline, not recommended for production

---

## ⚖️ Comparative Analysis

### 🏆 Best Performers by Metric

- **Highest QoS Compliance:** Random (77.7%)
- **Best Fairness:** DynamicPriority (0.781)
- **Lowest Avg Latency:** FixedPriority (95.9 cycles)
- **Lowest Starvation:** DynamicPriority (89.9%)

### 📊 Traffic Pattern Impact Analysis

**RANDOM**

- Average Requests Generated: 15799
- Average Service Rate: 12.7%
- Average QoS Compliance: 42.6%
- Average Starvation: 87.3%

**HEAVY_CONTENTION**

- Average Requests Generated: 26480
- Average Service Rate: 7.6%
- Average QoS Compliance: 56.8%
- Average Starvation: 92.4%
- 💡 All policies struggle under heavy load - significant starvation expected

**PRIORITY_INVERSION**

- Average Requests Generated: 19793
- Average Service Rate: 10.1%
- Average QoS Compliance: 67.8%
- Average Starvation: 89.9%
- 💡 Tests priority enforcement when low-priority traffic dominates

---

## 📝 Recommendations

### 1️⃣ For Real-Time Critical Systems

- **Recommended:** FixedPriority arbiter
- **Rationale:** Accepts fairness trade-off for guaranteed QoS
- **Caution:** Monitor best-effort starvation and adjust if needed

### 2️⃣ For Balanced QoS + Fairness

- **Recommended:** DynamicPriority arbiter
- **Rationale:** Good middle ground for mixed workloads
- **Benefit:** Adapts to changing traffic conditions

### 3️⃣ For Fairness-Critical Systems

- **Recommended:** WeightedRoundRobin arbiter
- **Rationale:** Configure weights based on traffic class priorities
- **Caution:** Accept slightly higher latency for better fairness

### 4️⃣ Avoid in Production

- **Not Recommended:** Random arbiter
- **Reason:** No QoS guarantees, poor fairness
- **Use Case:** Only useful for testing or non-critical applications

---

## ⚠️ Starvation Analysis

### Starvation by Traffic Class (averaged across all tests)

- **Real-Time:** 70.3% (target: near 0%)
- **Isochronous:** 95.0%
- **Best-Effort:** 96.9%

⚠️ **WARNING:** Real-time starvation detected! Critical issue for QoS systems.

⚠️ **WARNING:** Excessive best-effort starvation. Consider load balancing.

---

## 📊 Summary Comparison Table

| Policy | QoS % | Fairness | Avg Latency | Starvation % | Best Use Case |
|--------|-------|----------|-------------|--------------|---------------|
| FixedPriority | 77.6% | 0.366 | 95.9 | 89.9% | Real-time critical |
| WeightedRoundRobin | 29.5% | 0.690 | 443.4 | 89.9% | Fairness-critical |
| DynamicPriority | 38.0% | 0.781 | 499.0 | 89.9% | General purpose |
| Random | 77.7% | 0.366 | 99.1 | 89.9% | Testing only |

---

## 📁 Related Files

- **Detailed CSV Results:** `arbiter_performance_report.csv`
- **Visualizations:** `arbiter_performance_analysis.png`
- **Source Code:** `test_arbiters.py`

---

*Report generated by Arbiter Performance Testing Framework*
