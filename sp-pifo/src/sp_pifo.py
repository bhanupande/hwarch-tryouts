# ============================================================
# SPPifo Class Implementation
# Author: Bhanu Pande
# Date: May 2, 2025
# Description: This module implements the SPPifo class, which
#              provides a priority-based queuing mechanism
#              with multiple queues and configurable priorities.
# ============================================================
class SPPifo:
    def __init__(self, M, N, LEN):
        if M <= 0:
            raise ValueError(f"Number of queues (M) must be greater than 0. Received: {M}")
        self.M = M  # Number of queues
        self.N = N  # Number of priorities
        self.LEN = LEN  # Length of each queue
        self.priority = [0] * self.M  # Priority of each queue, initialized to 0
        self.queues = [[] for _ in range(self.M)]  # Create M empty queues
        self.enqueue_index = 0  # Index of the queue to enqueue into
        self.dequeue_index = 0  # Index of the queue to dequeue from

    def enqueue(self, value):
        if value <= self.N:
            self.select_enqueue_index(value)
            if self.enqueue_index < 0 or self.enqueue_index >= self.M:
                raise Exception(f"Invalid enqueue index: {self.enqueue_index}, M: {self.M}")
            self.queues[self.enqueue_index].append(value)
            #print(f"Value {value} enqueued in queue {self.enqueue_index}")
            #print (self.queues)
        else:
            raise Exception(f"Value: {value} exceeds maximum priority")

    def dequeue(self):
        # Dequeue a value from the appropriate queue based on priority.
        self.select_dequeue_index()  # Determine the queue to dequeue from
        if self.queues[self.dequeue_index]:  # Ensure the selected queue is not empty
            #print (self.queues)
            return self.queues[self.dequeue_index].pop(0)  # Remove and return the first value in the queue
        else:
            raise Exception(f"Queue:{self.dequeue_index} is empty")  # Raise an error if the queue is empty

    def select_dequeue_index(self):
        # Select the index of the queue to dequeue from, based on the highest priority (lowest value).
        priority_values = [self.queues[i][0] for i in range(self.M) if self.queues[i]]  # Get the first value of each non-empty queue
        if priority_values:
            self.dequeue_index = priority_values.index(min(priority_values))  # Select the queue with the lowest value
        else:
            raise Exception("All queues are empty")  # Raise an error if all queues are empty

    def select_enqueue_index(self, value):
        # Try to find a queue where the value can be enqueued based on priority
        for i in range(self.M):
            if value >= self.priority[i]:
                self.priority[i] = value
                self.enqueue_index = i
                #print(f"Enqueue index selected: {self.enqueue_index}, Priority updated: {self.priority}")
                return

        # If no valid queue is found, enqueue into the queue with the smallest priority
        self.enqueue_index = self.priority.index(min(self.priority))
        self.priority[self.enqueue_index] = value
        #print(f"Enqueue index selected (fallback): {self.enqueue_index}, Priority updated: {self.priority}")
# ============================================================
# End of SPPifo Class Implementation
# Notes:
# - Ensure that the input values for enqueue and dequeue operations
#   are within the valid range of priorities.
# - This implementation assumes that the queues are initialized
#   with a fixed length and default values of 0.
# ============================================================