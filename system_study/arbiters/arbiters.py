"""
ARBITRATION ENGINE CORE MODULE

PURPOSE:
This module implements a flexible arbitration system that mediates access to shared
resources among multiple competing requestors. It provides the fundamental building
blocks for fair, efficient, and configurable resource allocation in systems where
multiple entities compete for limited resources.

ARCHITECTURAL DESIGN:
- Policy-based arbitration: Pluggable algorithms for different fairness requirements
- Configurable scaling: Support for variable numbers of requestors and outputs
- Single-cycle operation: Deterministic arbitration decisions within one cycle
- Stateful operation: Maintains context for algorithms requiring history

SUPPORTED ARBITRATION POLICIES:
1. FixedPriority: Deterministic priority-based selection (lowest index wins)
2. RoundRobin: Fair rotation ensuring equal access opportunity
3. Random: Stochastic selection for load balancing and unpredictability
4. WeightedRoundRobin: Fair rotation with configurable requestor weights
5. WeightedRandom: Weighted stochastic selection based on requestor priorities

DESIGN PHILOSOPHY:
- Simplicity: Clear, understandable algorithms
- Flexibility: Easy extension for new arbitration policies
- Performance: Efficient O(n) or better algorithms
- Determinism: Predictable behavior for real-time systems (except Random policy)

USAGE SCENARIOS:
- Network packet arbitration and quality of service
- Memory controller request scheduling
- CPU resource allocation and process scheduling
- I/O request prioritization and fairness
- Any shared resource contention resolution

EVOLUTION CONTEXT:
This module serves as the foundation for advanced testing frameworks that
evaluate arbitration performance under various traffic patterns and QoS
requirements, supporting both basic boolean patterns and sophisticated
traffic class analysis.
"""

import random


class Arbiter:
    """
    CONFIGURABLE ARBITRATION ENGINE
    
    PURPOSE:
    This class implements a flexible arbitration system that can mediate access
    to shared resources using different policies. It provides the core arbitration
    logic with configurable algorithms, scaling, and state management.
    
    ARCHITECTURAL FEATURES:
    - Policy flexibility: Support for multiple arbitration algorithms
    - Scalable design: Configurable number of requestors and outputs
    - State management: Maintains necessary context for stateful policies
    - Validation: Input validation and error handling for robust operation
    
    DESIGN PRINCIPLES:
    - Single responsibility: Focus purely on arbitration decisions
    - Policy abstraction: Algorithm selection without implementation coupling
    - Stateful context: Maintain history for fair scheduling policies
    - Performance focus: Efficient algorithms suitable for real-time operation
    
    SUPPORTED CONFIGURATIONS:
    - Requestors: 1 to N competing entities seeking resource access
    - Outputs: Currently optimized for single output (1-to-1 selection)
    - Policies: FixedPriority, RoundRobin, Random, with extension capability
    
    USAGE PATTERN:
    1. Instantiate with desired configuration (requestors, outputs, policy)
    2. Call arbitrate() with current request vector
    3. Receive granted requestor ID for resource allocation
    4. Repeat for subsequent arbitration cycles
    
    STATE MANAGEMENT:
    - gnt_id: Tracks last granted requestor for RoundRobin fairness
    - Policy-specific state: Maintained internally for algorithm requirements
    
    THREAD SAFETY:
    This class is not thread-safe. External synchronization required for
    concurrent access from multiple threads.
    """
    
    def __init__(self, num_requestors=4, num_outputs=1, policy='FixedPriority', name='Arbiter', weights=None, mode='random'):
        """
        ARBITER INITIALIZATION AND CONFIGURATION
        
        PURPOSE:
        Initialize the arbitration engine with specified parameters, establishing
        the operational context and policy selection for subsequent arbitration
        decisions throughout the system's lifetime.
        
        CONFIGURATION STRATEGY:
        - Sensible defaults: Enable quick instantiation for common use cases
        - Full customization: Support for specialized system requirements
        - Validation: Ensure configuration consistency and operational viability
        - Naming: Support identification in multi-arbiter systems
        - Weight support: Enable weighted arbitration policies with custom priorities
        
        PARAMETER DESIGN DECISIONS:
        - num_requestors: Default 4 provides good testing coverage without complexity
        - num_outputs: Default 1 represents most common arbitration scenario
        - policy: FixedPriority default ensures deterministic, predictable behavior
        - name: Human-readable identification for debugging and reporting
        - weights: Optional array for weighted policies, defaults to equal weights
        
        WEIGHTS SYSTEM DESIGN:
        - Flexible weighting: Support for arbitrary positive weight values
        - Equal defaults: When None, all requestors get equal weight (value 1)
        - Policy compatibility: Used by WeightedRoundRobin, WeightedRandom policies
        - Validation: Ensures weights array length matches num_requestors
        - Performance impact: Minimal overhead for non-weighted policies
        
        STATE INITIALIZATION:
        - gnt_id: Initialize to 0 for consistent starting state
        - Policy setup: Prepare any policy-specific state requirements
        - Weight storage: Process and validate weights for weighted policies
        - Validation: Ensure parameters are within acceptable ranges
        
        Args:
            num_requestors (int, default=4): Number of competing requestors
                Valid range: 1 to system limits, typically 2-64 for practical use
            num_outputs (int, default=1): Number of concurrent grants possible
                Currently optimized for single output arbitration
            policy (str, default='FixedPriority'): Arbitration algorithm selection
                Options: 'FixedPriority', 'RoundRobin', 'Random', 'WeightedRoundRobin', 'WeightedRandom'
            name (str, default='Arbiter'): Human-readable identifier
                Used for debugging, logging, and multi-arbiter identification
            weights (List[int/float], optional): Weight values for each requestor
                Length must match num_requestors if provided
                Higher values indicate higher priority/frequency of access
                Defaults to equal weights (all 1.0) if None
                Used by WeightedRoundRobin and WeightedRandom policies
        
        Raises:
            ValueError: If configuration parameters are invalid or inconsistent
            ValueError: If weights array length doesn't match num_requestors
            ValueError: If any weight value is negative or zero
            
        EXTENSION POINTS:
        - New policies: Add policy strings and corresponding logic
        - Multi-output: Extend for multiple concurrent grants
        - Dynamic weights: Runtime weight adjustment capabilities
        - Dynamic reconfiguration: Runtime policy or parameter changes
        """
        # =================================================================
        # CORE CONFIGURATION STORAGE
        # =================================================================
        # Store human-readable identifier for debugging and multi-arbiter systems
        self.name = name
        
        # Store system scaling parameters
        self.num_requestors = num_requestors  # Number of competing entities
        self.num_outputs = num_outputs        # Number of concurrent grants (typically 1)
        
        # Store arbitration policy selection
        self.policy = policy                  # Algorithm choice for arbitration decisions

        self.mode = mode                      # Mode for arbitration behavior (e.g., 'random' for Random policy)
        
        # =================================================================
        # WEIGHTS SYSTEM INITIALIZATION
        # =================================================================
        # Process and validate weights for weighted arbitration policies
        if weights is None:
            # Default to equal weights for all requestors
            self.weights = [1.0] * num_requestors
        else:
            # Validate provided weights array
            if len(weights) != num_requestors:
                raise ValueError(f"Weights array length ({len(weights)}) must match num_requestors ({num_requestors})")
            
            # Validate that all weights are positive
            if any(w <= 0 for w in weights):
                raise ValueError("All weights must be positive (greater than 0)")
            
            # Store validated weights (convert to float for consistency)
            self.weights = [float(w) for w in weights]
        
        # =================================================================
        # ALGORITHM STATE INITIALIZATION
        # =================================================================
        # Initialize state for RoundRobin policy fairness tracking
        # This tracks the last granted requestor ID to ensure fair rotation
        self.gnt_id = 0  # Start with requestor 0 for consistent initial state

    def arbitrate(self, requests):
        """
        MAIN ARBITRATION DECISION ENGINE
        
        PURPOSE:
        This method implements the primary arbitration interface, processing
        a vector of requests and returning the ID of the selected requestor.
        It provides input validation, policy application, and result delivery.
        
        ARBITRATION WORKFLOW:
        1. Input validation: Ensure request vector is well-formed and consistent
        2. Active request detection: Verify at least one requestor is active
        3. Policy application: Delegate algorithm-specific selection logic
        4. Result delivery: Return selected requestor ID for resource allocation
        
        INPUT VALIDATION STRATEGY:
        - Null/empty protection: Handle edge cases gracefully
        - Size validation: Ensure request vector matches configured requestor count
        - Activity detection: Verify at least one active request exists
        - Type checking: Implicit through Python's duck typing
        
        POLICY ABSTRACTION:
        The method delegates actual selection logic to arb_policy(), enabling
        clean separation between validation/interface and algorithm implementation.
        This design allows easy addition of new policies without changing the
        public interface or validation logic.
        
        ERROR HANDLING:
        - Invalid inputs: Raise ValueError with descriptive messages
        - No active requests: Return None to indicate no selection
        - Policy errors: Allow policy-specific exceptions to propagate
        
        PERFORMANCE CONSIDERATIONS:
        - O(1) validation for most checks
        - O(n) activity detection where n = num_requestors
        - Policy-specific complexity for actual selection
        
        Args:
            requests (List[bool]): Boolean vector indicating active requestors
                Length must match self.num_requestors
                True indicates requestor is seeking resource access
                False indicates requestor is idle or not competing
        
        Returns:
            int or None: Selected requestor ID (0-based index) or None if no selection
                Valid return range: 0 to (num_requestors - 1)
                None indicates no active requests or error condition
        
        Raises:
            ValueError: If request vector length doesn't match configuration
            
        USAGE PATTERNS:
        - Single-cycle operation: Call once per arbitration cycle
        - Stateful context: Method updates internal state for future calls
        - Result interpretation: Use returned ID for resource grant decisions
        """
        # =================================================================
        # INPUT VALIDATION AND EDGE CASE HANDLING
        # =================================================================
        
        # Handle null or empty request vectors
        if not requests:
            return None
            
        # Validate request vector size matches arbiter configuration
        # This ensures consistent interface and prevents indexing errors
        if len(requests) != self.num_requestors:
            raise ValueError(f"Expected {self.num_requestors} requests, but got {len(requests)}")
            
        # Check if any requests are active (at least one True value)
        # Return None if no requestors are competing for access
        if not any(requests):
            return None
            
        # =================================================================
        # POLICY APPLICATION AND RESULT GENERATION
        # =================================================================
        
        # Delegate to policy-specific arbitration logic
        # This updates self.gnt_id with the selected requestor
        self.arb_policy(requests)
        
        # Return the selected requestor ID for resource allocation
        return self.gnt_id

    def arb_policy(self, requests):
        """
        POLICY-SPECIFIC ARBITRATION LOGIC ENGINE
        
        PURPOSE:
        This method implements the core arbitration algorithms, providing
        the policy-specific logic for selecting among competing requestors.
        It encapsulates different fairness and performance strategies.
        
        ALGORITHM DESIGN PHILOSOPHY:
        - Efficiency: O(n) or better algorithms for real-time suitability
        - Fairness: Each policy provides different fairness guarantees
        - Determinism: Predictable behavior for most policies (except Random)
        - Stateful operation: Maintain context for policies requiring history
        
        POLICY IMPLEMENTATIONS:
        
        1. FIXED PRIORITY POLICY:
           - Algorithm: Linear scan from lowest to highest index
           - Fairness: Priority-based, lower indices have absolute priority
           - Performance: O(n) worst case, O(1) best case
           - Use case: Critical systems with strict priority requirements
           - Determinism: Fully deterministic and predictable
        
        2. ROUND ROBIN POLICY:
           - Algorithm: Rotating fair access starting from last granted + 1
           - Fairness: Equal opportunity for all requestors over time
           - Performance: O(n) worst case, maintains fairness guarantee
           - Use case: Systems requiring fair resource sharing
           - State: Tracks last granted requestor for rotation continuity
        
        3. RANDOM POLICY:
           - Algorithm: Uniform random selection among active requestors
           - Fairness: Probabilistic fairness over long time periods
           - Performance: O(n) for active requestor identification
           - Use case: Load balancing and unpredictable access patterns
           - Non-determinism: Provides randomness for security/load balancing
        
        4. WEIGHTED ROUND ROBIN POLICY:
           - Algorithm: Fair rotation with weighted probability distribution
           - Fairness: Proportional access based on configurable weights
           - Performance: O(n) for weight calculation and selection
           - Use case: QoS systems requiring differentiated service levels
           - Weights: Higher values increase access frequency proportionally
        
        5. WEIGHTED RANDOM POLICY:
           - Algorithm: Weighted stochastic selection without rotation bias
           - Fairness: Probabilistic proportional access based on weights
           - Performance: O(n) for weight calculation and selection
           - Use case: Load balancing with priority differentiation
           - Flexibility: Pure weighted selection without fairness constraints
        
        STATE MANAGEMENT:
        - Updates self.gnt_id with selected requestor
        - RoundRobin maintains rotation state across calls
        - FixedPriority and Random are stateless within policy logic
        
        ERROR HANDLING:
        - Invalid policy: Falls through to maintain current gnt_id
        - No active requestors: Handled by caller validation
        - Index bounds: Protected by caller validation
        
        EXTENSION PATTERN:
        New policies can be added by:
        1. Adding new elif branch with policy name
        2. Implementing selection algorithm
        3. Updating self.gnt_id with result
        4. Adding policy to constructor documentation
        
        Args:
            requests (List[bool]): Validated request vector from arbitrate()
                Guaranteed to have correct length and at least one active request
        
        Returns:
            None: Updates self.gnt_id as side effect
            
        PERFORMANCE CHARACTERISTICS:
        - FixedPriority: O(1) to O(n) depending on priority of active requestor
        - RoundRobin: O(n) worst case for complete rotation
        - Random: O(n) for active requestor identification + O(1) selection
        """
        # =================================================================
        # FIXED PRIORITY ARBITRATION POLICY
        # =================================================================
        if self.policy == 'FixedPriority':
            # Linear scan from index 0 (highest priority) to find first active requestor
            # Lower indices have absolute priority over higher indices
            # Provides deterministic, predictable arbitration for critical systems
            for i in range(len(requests)):
                if requests[i]:
                    self.gnt_id = i
                    return
                    
        # =================================================================
        # ROUND ROBIN ARBITRATION POLICY  
        # =================================================================
        elif self.policy == 'RoundRobin':
            # Fair rotation starting from position after last granted requestor
            # This ensures equal opportunity for all requestors over time
            # Mathematical approach: use modular arithmetic for wraparound
            
            # Calculate starting position for fair rotation
            start_index = (self.gnt_id + 1) % len(requests)
            
            # Scan all positions starting from rotation point
            # This guarantees fairness by ensuring no requestor is permanently starved
            for i in range(len(requests)):
                curr_index = (start_index + i) % len(requests)
                if requests[curr_index]:
                    self.gnt_id = curr_index
                    return
                    
        # =================================================================
        # WEIGHTED ROUND ROBIN ARBITRATION POLICY
        # =================================================================
        elif self.policy == 'WeightedRoundRobin':
            # Weighted fair rotation considering requestor priorities
            # Higher weights receive proportionally more access opportunities
            # Combines fairness of round-robin with priority-based weighting
            
            # Calculate total weight of all active requestors
            # Only active requestors participate in weighted selection
            total_active_weight = sum(self.weights[i] for i in range(len(requests)) if requests[i])
            if total_active_weight == 0:
                return  # No active requests
            
            # Use weighted random selection based on normalized weights
            # This provides proportional access based on weight values
            if (self.mode == 'random'):
                threshold_value = random.uniform(0, total_active_weight)
            elif (self.mode == 'mean'):
                threshold_value = total_active_weight / 2
            elif (self.mode == 'median'):
                threshold_value = sorted(self.weights)[len(self.weights) // 2]
            else:
                threshold_value = total_active_weight / 2  # Default to median if unknown mode
            cumulative_weight = 0.0
            
            # Start from position after last granted for fairness
            start_index = (self.gnt_id + 1) % len(requests)
            
            # Scan all positions with weighted probability
            for i in range(len(requests)):
                curr_index = (start_index + i) % len(requests)
                if requests[curr_index]:
                    cumulative_weight += self.weights[curr_index]
                    if threshold_value <= cumulative_weight:
                        self.gnt_id = curr_index
                        return
        
        # =================================================================
        # RANDOM ARBITRATION POLICY
        # =================================================================
        elif self.policy == 'Random':
            # Stochastic selection among active requestors for load balancing
            # Provides unpredictability useful for security and performance distribution
            
            # Build list of currently active requestor indices
            # This enables uniform random selection among only competing requestors
            active_requestors = [i for i, req in enumerate(requests) if req]
            
            # Select randomly from active requestors if any exist
            if active_requestors:
                self.gnt_id = random.choice(active_requestors)
                return
        
        # =================================================================
        # WEIGHTED RANDOM ARBITRATION POLICY
        # =================================================================
        elif self.policy == 'WeightedRandom':
            # Weighted stochastic selection among active requestors
            # Higher weights increase probability of selection without rotation constraints
            # Provides weighted load balancing with full randomness
            
            # Calculate total weight of all active requestors
            total_active_weight = sum(self.weights[i] for i in range(len(requests)) if requests[i])
            if total_active_weight == 0:
                return  # No active requests
            
            # Use weighted random selection based on normalized weights
            rand_value = random.uniform(0, total_active_weight)
            cumulative_weight = 0.0
            
            # Scan all requestors with weighted probability (no rotation bias)
            for i in range(len(requests)):
                if requests[i]:
                    cumulative_weight += self.weights[i]
                    if rand_value <= cumulative_weight:
                        self.gnt_id = i
                        return
        
        # =================================================================
        # FALLBACK HANDLING
        # =================================================================
        # If no active requests found or unknown policy, maintain current gnt_id
        # This situation should not occur due to caller validation, but provides
        # graceful degradation and maintains system stability
        # Note: Unknown policies will silently maintain previous grant state
