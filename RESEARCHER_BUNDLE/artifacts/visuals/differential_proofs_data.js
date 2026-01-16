const differentialProofsData = {
  items: [
    // Identity (HoTT foundation)
    { name: "Id", kind: "abbrev", family: "HoTT/Identity", pos: { x: 0.1, y: 0.9, z: 0.1 } },
    { name: "FormId", kind: "abbrev", family: "HoTT/Identity", pos: { x: 0.12, y: 0.88, z: 0.12 } },
    { name: "Id.refl", kind: "theorem", family: "HoTT/Identity", pos: { x: 0.14, y: 0.86, z: 0.14 } },
    { name: "Id.symm", kind: "theorem", family: "HoTT/Identity", pos: { x: 0.16, y: 0.84, z: 0.16 } },
    { name: "Id.trans", kind: "theorem", family: "HoTT/Identity", pos: { x: 0.18, y: 0.82, z: 0.18 } },

    // SKY Combinators (core)
    { name: "Comb", kind: "inductive", family: "SKY/Core", pos: { x: 0.25, y: 0.75, z: 0.2 } },
    { name: "Step", kind: "inductive", family: "SKY/Core", pos: { x: 0.28, y: 0.72, z: 0.22 } },
    { name: "Steps", kind: "inductive", family: "SKY/Core", pos: { x: 0.31, y: 0.69, z: 0.24 } },
    { name: "Normal", kind: "def", family: "SKY/Core", pos: { x: 0.34, y: 0.66, z: 0.26 } },
    { name: "I", kind: "def", family: "SKY/Core", pos: { x: 0.37, y: 0.63, z: 0.28 } },
    { name: "K_normal", kind: "theorem", family: "SKY/Core", pos: { x: 0.3, y: 0.68, z: 0.3 } },
    { name: "S_normal", kind: "theorem", family: "SKY/Core", pos: { x: 0.32, y: 0.66, z: 0.32 } },
    { name: "Y_normal", kind: "theorem", family: "SKY/Core", pos: { x: 0.34, y: 0.64, z: 0.34 } },
    { name: "I_reduces", kind: "theorem", family: "SKY/Core", pos: { x: 0.36, y: 0.62, z: 0.36 } },

    // SKY Multiway
    { name: "RuleTag", kind: "inductive", family: "SKY/Multiway", pos: { x: 0.4, y: 0.6, z: 0.3 } },
    { name: "Dir", kind: "inductive", family: "SKY/Multiway", pos: { x: 0.42, y: 0.58, z: 0.32 } },
    { name: "EventData", kind: "structure", family: "SKY/Multiway", pos: { x: 0.44, y: 0.56, z: 0.34 } },
    { name: "stepEdgesList", kind: "def", family: "SKY/Multiway", pos: { x: 0.46, y: 0.54, z: 0.36 } },
    { name: "stepEdges", kind: "def", family: "SKY/Multiway", pos: { x: 0.48, y: 0.52, z: 0.38 } },
    { name: "stepEdgesList_sound", kind: "theorem", family: "SKY/Multiway", pos: { x: 0.45, y: 0.53, z: 0.4 } },
    { name: "stepEdges_complete", kind: "theorem", family: "SKY/Multiway", pos: { x: 0.47, y: 0.51, z: 0.42 } },

    // Differential: VectorSpace
    { name: "FormalSum", kind: "abbrev", family: "Differential/VectorSpace", pos: { x: 0.5, y: 0.5, z: 0.4 } },
    { name: "single", kind: "def", family: "Differential/VectorSpace", pos: { x: 0.52, y: 0.48, z: 0.42 } },
    { name: "l2NormSq", kind: "def", family: "Differential/VectorSpace", pos: { x: 0.54, y: 0.46, z: 0.44 } },
    { name: "dot", kind: "def", family: "Differential/VectorSpace", pos: { x: 0.56, y: 0.44, z: 0.46 } },

    // Differential: LinearComb
    { name: "FormalSum.app", kind: "def", family: "Differential/LinearComb", pos: { x: 0.55, y: 0.45, z: 0.5 } },
    { name: "FormalSum.appBilin", kind: "def", family: "Differential/LinearComb", pos: { x: 0.57, y: 0.43, z: 0.52 } },
    { name: "FormalSum.stepSum", kind: "def", family: "Differential/LinearComb", pos: { x: 0.59, y: 0.41, z: 0.54 } },
    { name: "FormalSum.steps", kind: "def", family: "Differential/LinearComb", pos: { x: 0.61, y: 0.39, z: 0.56 } },
    { name: "FormalSum.reachabilityBounded", kind: "def", family: "Differential/LinearComb", pos: { x: 0.63, y: 0.37, z: 0.58 } },
    { name: "app_single_single", kind: "theorem", family: "Differential/LinearComb", pos: { x: 0.58, y: 0.42, z: 0.55 } },

    // Differential: Derivative (Dual numbers)
    { name: "Dual", kind: "structure", family: "Differential/Derivative", pos: { x: 0.6, y: 0.4, z: 0.6 } },
    { name: "Dual.pure", kind: "def", family: "Differential/Derivative", pos: { x: 0.62, y: 0.38, z: 0.62 } },
    { name: "Dual.withTangent", kind: "def", family: "Differential/Derivative", pos: { x: 0.64, y: 0.36, z: 0.64 } },
    { name: "dualApp", kind: "def", family: "Differential/Derivative", pos: { x: 0.66, y: 0.34, z: 0.66 } },
    { name: "derivativeApp1", kind: "def", family: "Differential/Derivative", pos: { x: 0.68, y: 0.32, z: 0.68 } },
    { name: "derivativeApp2", kind: "def", family: "Differential/Derivative", pos: { x: 0.7, y: 0.3, z: 0.7 } },
    { name: "K_denote", kind: "def", family: "Differential/Derivative", pos: { x: 0.65, y: 0.35, z: 0.67 } },
    { name: "S_denote", kind: "def", family: "Differential/Derivative", pos: { x: 0.67, y: 0.33, z: 0.69 } },
    { name: "S_derivative", kind: "def", family: "Differential/Derivative", pos: { x: 0.69, y: 0.31, z: 0.71 } },
    { name: "chainRule", kind: "theorem", family: "Differential/Derivative", pos: { x: 0.71, y: 0.29, z: 0.73 } },

    // Differential: Exponential (Codereliction)
    { name: "Exp", kind: "abbrev", family: "Differential/Exponential", pos: { x: 0.72, y: 0.28, z: 0.65 } },
    { name: "codereliction_linear_increment", kind: "theorem", family: "Differential/Exponential", pos: { x: 0.74, y: 0.26, z: 0.67 } },
    { name: "coweakening", kind: "def", family: "Differential/Codereliction", pos: { x: 0.73, y: 0.27, z: 0.68 } },
    { name: "codereliction_is_derivative", kind: "theorem", family: "Differential/Codereliction", pos: { x: 0.75, y: 0.25, z: 0.7 } },

    // Differential: Loss functions
    { name: "IOExample", kind: "structure", family: "Differential/Loss", pos: { x: 0.78, y: 0.3, z: 0.75 } },
    { name: "error", kind: "def", family: "Differential/Loss", pos: { x: 0.8, y: 0.28, z: 0.77 } },
    { name: "singleIOLoss", kind: "def", family: "Differential/Loss", pos: { x: 0.82, y: 0.26, z: 0.79 } },
    { name: "ioLoss", kind: "def", family: "Differential/Loss", pos: { x: 0.84, y: 0.24, z: 0.81 } },
    { name: "l2Reg", kind: "def", family: "Differential/Loss", pos: { x: 0.81, y: 0.27, z: 0.78 } },
    { name: "totalLoss", kind: "def", family: "Differential/Loss", pos: { x: 0.83, y: 0.25, z: 0.8 } },
    { name: "ioLossCoordGrad", kind: "def", family: "Differential/Loss", pos: { x: 0.85, y: 0.23, z: 0.82 } },
    { name: "totalGrad", kind: "def", family: "Differential/Loss", pos: { x: 0.87, y: 0.21, z: 0.84 } },

    // Differential: Gradient Descent
    { name: "GDConfig", kind: "structure", family: "Differential/GradientDescent", pos: { x: 0.88, y: 0.2, z: 0.85 } },
    { name: "GDState", kind: "structure", family: "Differential/GradientDescent", pos: { x: 0.9, y: 0.18, z: 0.87 } },
    { name: "projectToParams", kind: "def", family: "Differential/GradientDescent", pos: { x: 0.89, y: 0.19, z: 0.86 } },
    { name: "gradientStep", kind: "def", family: "Differential/GradientDescent", pos: { x: 0.91, y: 0.17, z: 0.88 } },
    { name: "gradientDescentLoop", kind: "def", family: "Differential/GradientDescent", pos: { x: 0.93, y: 0.15, z: 0.9 } },
    { name: "synthesize", kind: "def", family: "Differential/GradientDescent", pos: { x: 0.95, y: 0.13, z: 0.92 } },

    // Differential: Nucleus integration
    { name: "nucleusLinear_idempotent", kind: "theorem", family: "Differential/Nucleus", pos: { x: 0.85, y: 0.35, z: 0.75 } },
    { name: "termFixedPoints", kind: "def", family: "Differential/Nucleus", pos: { x: 0.87, y: 0.33, z: 0.77 } },
    { name: "projectToFixed", kind: "def", family: "Differential/Nucleus", pos: { x: 0.89, y: 0.31, z: 0.79 } },
    { name: "synthesizeStable", kind: "def", family: "Differential/GradientDescent", pos: { x: 0.94, y: 0.14, z: 0.91 } },

    // Differential: SKY Derivatives
    { name: "K_jacobian", kind: "def", family: "Differential/SKYDerivatives", pos: { x: 0.75, y: 0.4, z: 0.72 } },
    { name: "S_jacobian_exists", kind: "theorem", family: "Differential/SKYDerivatives", pos: { x: 0.77, y: 0.38, z: 0.74 } },

    // Compute backend (runtime)
    { name: "Compute.FSum", kind: "abbrev", family: "Compute/Runtime", pos: { x: 0.6, y: 0.55, z: 0.45 } },
    { name: "Compute.addTerm", kind: "def", family: "Compute/Runtime", pos: { x: 0.62, y: 0.53, z: 0.47 } },
    { name: "Compute.normalize", kind: "def", family: "Compute/Runtime", pos: { x: 0.64, y: 0.51, z: 0.49 } },
    { name: "Compute.app", kind: "def", family: "Compute/Runtime", pos: { x: 0.66, y: 0.49, z: 0.51 } },
    { name: "Compute.stepSum", kind: "def", family: "Compute/Runtime", pos: { x: 0.68, y: 0.47, z: 0.53 } },
    { name: "Compute.showFSum", kind: "def", family: "Compute/Runtime", pos: { x: 0.7, y: 0.45, z: 0.55 } },
    { name: "Compute.GDConfig", kind: "structure", family: "Compute/Runtime", pos: { x: 0.72, y: 0.43, z: 0.57 } },
    { name: "Compute.gradientDescentLoop", kind: "def", family: "Compute/Runtime", pos: { x: 0.74, y: 0.41, z: 0.59 } },
    { name: "Compute.synthesize", kind: "def", family: "Compute/Runtime", pos: { x: 0.76, y: 0.39, z: 0.61 } }
  ],
  edges: [
    // Identity foundation
    [0, 1], [0, 2], [2, 3], [3, 4],
    // SKY depends on Identity
    [0, 5], [5, 6], [6, 7], [5, 8], [5, 9],
    [5, 10], [5, 11], [5, 12], [9, 13],
    // Multiway depends on SKY
    [5, 14], [14, 15], [15, 16], [16, 17], [17, 18], [17, 19], [18, 20],
    // VectorSpace
    [5, 21], [21, 22], [21, 23], [21, 24],
    // LinearComb depends on VectorSpace and Multiway
    [21, 25], [25, 26], [17, 27], [27, 28], [28, 29], [25, 30],
    // Derivative depends on LinearComb
    [25, 31], [31, 32], [31, 33], [31, 34], [34, 35], [34, 36],
    [34, 37], [34, 38], [38, 39], [39, 40],
    // Exponential/Codereliction
    [21, 41], [41, 42], [41, 43], [43, 44],
    // Loss depends on LinearComb
    [25, 45], [45, 46], [46, 47], [47, 48], [21, 49], [48, 50], [50, 51], [51, 52],
    // GradientDescent depends on Loss
    [45, 53], [53, 54], [54, 55], [55, 56], [56, 57], [57, 58],
    // Nucleus integration
    [21, 59], [59, 60], [60, 61], [58, 62],
    // SKY Derivatives
    [38, 63], [39, 64],
    // Compute backend (parallel implementation)
    [21, 65], [65, 66], [66, 67], [65, 68], [68, 69], [65, 70],
    [65, 71], [71, 72], [72, 73]
  ]
};
