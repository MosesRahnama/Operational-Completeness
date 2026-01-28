# What Are B, S, Delta, and N?

## The Full Structure: `recΔ b s n`

This is **primitive recursion** - the mathematical version of a for-loop.

---

## 🅱️ What is `b`?

**`b` = BASE CASE = "what to return when we're done"**

Like in factorial:
- `factorial(0) = 1`
- The `1` is the base case

In a for-loop:
```python
result = 0  # This is 'b' - the starting value
for i in range(n):
    result = result + i
```

---

## 🔤 What is `s`?

**`s` = STEP FUNCTION = "what to do at each step"**

Like in factorial:
- `factorial(n) = n × factorial(n-1)`
- The "multiply by n" operation is the step function

In a for-loop:
```python
for i in range(n):
    result = process(result)  # 'process' is 's'
```

---

## 🔺 What is `delta`?

**`delta` = SUCCESSOR = "one more" = "+1"**

It's just a way to represent numbers:
- `void` = 0
- `delta void` = 1
- `delta (delta void)` = 2
- `delta (delta (delta void))` = 3

Think of it like tally marks:
- ` ` = 0
- `|` = 1
- `||` = 2
- `|||` = 3

---

## 🔢 What is `n`?

**`n` = NUMBER/COUNTER = "how many times to recurse"**

It's the thing we're counting down:
- Start with some `n`
- Each recursion reduces it
- When we hit `void` (0), we stop

---

## 📝 The Whole Thing Together

`recΔ b s n` means:
- Start with counter `n`
- If `n = void` (0), return base case `b`
- If `n = delta m` (n > 0), apply step `s` and continue with `m`

### In Python Terms:
```python
def recDelta(base, step, n):
    if n == 0:
        return base
    else:
        return step(recDelta(base, step, n-1))
```

---

## 🔄 The Problematic Rule Again

`recΔ b s (delta n) → app s (recΔ b s n)`

Now reads as:
- When counter is "one more than n"
- Apply the step function to the recursion with counter n
- This creates two copies of the step function

---

## 🎯 Real Example: Calculating 3!

```
recΔ 1 (multiply_by_current) 3

Step 1: recΔ 1 (×) (delta (delta (delta void)))
        → app (×3) (recΔ 1 (×) (delta (delta void)))

Step 2: → app (×3) (app (×2) (recΔ 1 (×) (delta void)))

Step 3: → app (×3) (app (×2) (app (×1) (recΔ 1 (×) void)))

Step 4: → app (×3) (app (×2) (app (×1) 1))

Final:  → 3 × 2 × 1 × 1 = 6
```

---

## 💡 Why These Names?

- **`b` for "base"** - the foundation we build on
- **`s` for "step"** - what we do each time
- **`delta` (Δ)** - Greek letter often meaning "change" or "difference"
- **`n` for "number"** - standard variable for counting

---

## 🚨 The Key Insight

The problem isn't the names or what they mean. The problem is that when you recurse with a step function, the step function appears multiple times in the result. That's the **duplication** that breaks simple counting.

It's like instructions that say:
1. "Tell the next person these same instructions"
2. "Also do task X"

Now task X appears at every level of the chain!