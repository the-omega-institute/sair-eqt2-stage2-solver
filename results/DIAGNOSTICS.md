# Per-round diagnostics — gpt-oss-120b live ledgers

Residuals only (Pass 3). Pilot run = `pilot_1_live.json` + `pilot_remaining5_live.json`;
canonical run = `sample_20_live.json`.

Judge error categories are heuristic greps over stored judge responses
(`introN` / `introN+unexpected_token_have`, type mismatch, decide refute,
unsolved goals, unknown tactic, timeout, other). For `normal_0749`, prefer the
explicit 12 = 11 + 1 double-intro split over a bare “11/16” or “12/16” label.

## normal_0749

### pilot

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 2500.6
- timeout: False
- judge error categories: {'introN_only': 11, 'introN+unexpected_token_have': 1, 'type_mismatch': 3, 'rejected_other': 1}
- double-intro note: **12 of 16** rounds produced a double-`intro G _ h` certificate
  (**11** classified introN-only, **1** introN plus unexpected token `'have'`).
  Counts that say “11/16 introN” without this split are the introN-only subset of
  the same 12 affected rounds.

### canonical

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 2490.2
- timeout: False
- judge error categories: {'introN_only': 11, 'introN+unexpected_token_have': 1, 'type_mismatch': 3, 'rejected_other': 1}
- double-intro note: same split as pilot — **12 of 16** double-intro certificates
  (**11** introN-only, **1** introN plus unexpected token `'have'`).

### repeated-strategy note (`normal_0749`)

The model almost never leaves the same core rewrite: apply `h` at
`((x ◇ x) ◇ x)`.

- pilot: **15/16** rounds contain the literal `h x ((x ◇ x) ◇ x) x x`; round 6
  uses the `_` variant `h _ ((x ◇ x) ◇ x) x x` → **16/16** share the motif
  (the “14/16 same core tactic” observation from the live review).
- canonical: **15/16** rounds contain `((x ◇ x) ◇ x)` in the proof body.

## normal_0260

### pilot

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 2349.69
- timeout: False
- judge error categories: {'unsolved_goals': 1, 'introN': 4, 'rejected_other': 3, 'unknown_tactic': 2, 'decide_refute': 5, 'type_mismatch': 1}

### canonical

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 2547.9
- timeout: False
- judge error categories: {'unsolved_goals': 2, 'unknown_tactic': 3, 'rejected_other': 3, 'introN': 3, 'decide_refute': 3, 'type_mismatch': 2}

## normal_0227

### pilot

- status: **INCONCLUSIVE (solver wall-clock)**
- rounds / llm_calls: 8 (judge_calls=7)
- elapsed_seconds: 3952.82
- timeout: True
- judge error categories: {'type_mismatch': 4, 'rejected_other': 1, 'decide_refute': 2, 'timeout': 1}

### canonical

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 2376.39
- timeout: False
- judge error categories: {'rejected_other': 3, 'type_mismatch': 6, 'decide_refute': 4, 'introN': 3}

## normal_0126

### pilot

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=15)
- elapsed_seconds: 2684.72
- timeout: False
- judge error categories: {'decide_refute': 7, 'rejected_other': 1, 'unknown_tactic': 4, 'unsolved_goals': 1, 'introN': 1, 'type_mismatch': 1}

### canonical

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 2880.75
- timeout: False
- judge error categories: {'unknown_tactic': 1, 'introN': 1, 'decide_refute': 6, 'type_mismatch': 1, 'unsolved_goals': 2, 'rejected_other': 5}

## normal_0747

### pilot

- status: **INCONCLUSIVE (solver wall-clock)**
- rounds / llm_calls: 13 (judge_calls=11)
- elapsed_seconds: 3651.07
- timeout: True
- judge error categories: {'rejected_other': 2, 'introN': 3, 'decide_refute': 5, 'type_mismatch': 1, 'timeout': 1}

### canonical

- status: **INCONCLUSIVE (solver wall-clock)**
- rounds / llm_calls: 13 (judge_calls=12)
- elapsed_seconds: 3711.37
- timeout: True
- judge error categories: {'rejected_other': 4, 'type_mismatch': 2, 'decide_refute': 6, 'timeout': 1}

## normal_0092

### pilot

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 3085.53
- timeout: False
- judge error categories: {'rejected_other': 4, 'introN': 3, 'type_mismatch': 5, 'decide_refute': 4}

### canonical

- status: **FAILED**
- rounds / llm_calls: 16 (judge_calls=16)
- elapsed_seconds: 3207.58
- timeout: False
- judge error categories: {'type_mismatch': 6, 'rejected_other': 6, 'introN': 3, 'decide_refute': 1}
