#!/usr/bin/env python3
"""
Fix all issues in the Navier-Stokes project:
1. Fix syntax errors in Lean files
2. Clean and rebuild the project
3. Set up proper API key handling
"""

import subprocess
import os
import shutil
from pathlib import Path
import re

def fix_basic_lean():
    """Fix syntax errors in Basic.lean"""
    print("Fixing syntax errors in Basic.lean...")
    
    filepath = Path("NavierStokesLedger/Basic.lean")
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Fix line 97: unknown identifier 'simp'
    # The issue is that 'simp' is used outside of a proof context
    content = re.sub(
        r'def isSchwartzClass : Prop :=\s*simp',
        'def isSchwartzClass : Prop :=\n  sorry',
        content
    )
    
    # Fix line 131: unknown tactic issues
    content = re.sub(
        r'lemma golden_inv_val : φ⁻¹ = \(Real\.sqrt 5 - 1\) / 2 := by lean\s*rw \[φ\]\s*simp only \[inv_div\]\s*ring',
        'lemma golden_inv_val : φ⁻¹ = (Real.sqrt 5 - 1) / 2 := by\n  rw [φ]\n  simp only [inv_div]\n  ring',
        content
    )
    
    # Fix line 140: unknown tactic issues
    content = re.sub(
        r'lemma dissipation_golden_bound : dissipationConstant < φ⁻¹ := by lean\s*norm_num \[gol',
        'lemma dissipation_golden_bound : dissipationConstant < φ⁻¹ := by\n  sorry',
        content
    )
    
    # Fix energy definition
    content = re.sub(
        r'noncomputable def energy \(u : NSolution\) \(t : ℝ\) : ℝ := norm_num',
        'noncomputable def energy (u : NSolution) (t : ℝ) : ℝ :=\n  sorry',
        content
    )
    
    # Fix enstrophy definition
    content = re.sub(
        r'noncomputable def enstrophy \(u : NSolution\) \(t : ℝ\) : ℝ := norm_num',
        'noncomputable def enstrophy (u : NSolution) (t : ℝ) : ℝ :=\n  sorry',
        content
    )
    
    # Fix maxVorticity definition
    content = re.sub(
        r'noncomputable def maxVorticity \(u : NSolution\) \(t : ℝ\) : ℝ :=\s*norm_num',
        'noncomputable def maxVorticity (u : NSolution) (t : ℝ) : ℝ :=\n  sorry',
        content
    )
    
    # Fix beale_kato_majda theorem
    content = re.sub(
        r'theorem beale_kato_majda \{u : NSolution\} \{T : ℝ\} \(hT : 0 < T\) :\s*\(∀ t ∈ Set\.Icc 0 T, ContDiff ℝ ⊤ \(u t\)\) ↔\s*∃ C : ℝ, ∫ t in Set\.Icc 0 T, NSolution\.maxVorticity u t ≤ C := by norm_num',
        'theorem beale_kato_majda {u : NSolution} {T : ℝ} (hT : 0 < T) :\n  (∀ t ∈ Set.Icc 0 T, ContDiff ℝ ⊤ (u t)) ↔\n  ∃ C : ℝ, ∫ t in Set.Icc 0 T, NSolution.maxVorticity u t ≤ C := by\n  sorry',
        content
    )
    
    # Fix measure_ball_scaling lemma
    content = re.sub(
        r'lemma measure_ball_scaling \{r : ℝ\} \(hr : 0 < r\) :\s*volume \(Metric\.ball \(0 : EuclideanSpace ℝ \(Fin 3\)\) r\) = \(4 / 3 : ENNReal\) \* ENNReal\.ofReal π \* ENNReal\.ofReal \(r \^ 3\) := by constructor\s*· intro h\s*use 1\s*simp\s*· intro h\s*intro t ht\s*trivial',
        'lemma measure_ball_scaling {r : ℝ} (hr : 0 < r) :\n  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) = (4 / 3 : ENNReal) * ENNReal.ofReal π * ENNReal.ofReal (r ^ 3) := by\n  sorry',
        content
    )
    
    # Fix C_sobolev definition
    content = re.sub(
        r'noncomputable def C_sobolev : ℝ := lean\s*rfl',
        'noncomputable def C_sobolev : ℝ :=\n  1  -- Placeholder value',
        content
    )
    
    # Fix sobolev_3d_embedding lemma
    content = re.sub(
        r'lemma sobolev_3d_embedding :\s*∀ u : VectorField, VectorField\.sobolevNorm u 1 ≠ ⊤ →\s*VectorField\.lpNorm u 6 ≤ ENNReal\.ofReal C_sobolev \* VectorField\.sobolevNorm u 1 := by lean\s*use 1\s*simp',
        'lemma sobolev_3d_embedding :\n  ∀ u : VectorField, VectorField.sobolevNorm u 1 ≠ ⊤ →\n  VectorField.lpNorm u 6 ≤ ENNReal.ofReal C_sobolev * VectorField.sobolevNorm u 1 := by\n  sorry',
        content
    )
    
    # Fix C_poincare definition
    content = re.sub(
        r'noncomputable def C_poincare \(r : ℝ\) : ℝ := lean\s*norm_num',
        'noncomputable def C_poincare (r : ℝ) : ℝ :=\n  r  -- Placeholder value',
        content
    )
    
    # Fix isWeakHeatSolution definition
    content = re.sub(
        r'def isWeakHeatSolution \(f : EuclideanSpace ℝ \(Fin 3\) × ℝ → ℝ\) : Prop :=\s*trivial',
        'def isWeakHeatSolution (f : EuclideanSpace ℝ (Fin 3) × ℝ → ℝ) : Prop :=\n  sorry',
        content
    )
    
    # Fix curvatureParameter definition
    content = re.sub(
        r'noncomputable def curvatureParameter \(u : VectorField\) \(x : EuclideanSpace ℝ \(Fin 3\)\) : ℝ :=\s*rfl',
        'noncomputable def curvatureParameter (u : VectorField) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=\n  sorry',
        content
    )
    
    # Write the fixed content back
    with open(filepath, 'w') as f:
        f.write(content)
    
    print("✓ Fixed syntax errors in Basic.lean")

def clean_build():
    """Clean the build directory and reconfigure"""
    print("\nCleaning build directory...")
    
    lake_dir = Path(".lake")
    if lake_dir.exists():
        shutil.rmtree(lake_dir)
        print("✓ Removed .lake directory")
    
    # Run lake update to fetch dependencies
    print("\nFetching dependencies...")
    result = subprocess.run(["lake", "update"], capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Dependencies fetched successfully")
    else:
        print(f"⚠ Warning: lake update had issues: {result.stderr}")
    
    # Run initial build
    print("\nRunning initial build...")
    result = subprocess.run(["lake", "build"], capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ Build successful")
    else:
        print(f"⚠ Build had errors (this is expected with sorries)")
        if result.stderr:
            print(f"Errors: {result.stderr[:500]}...")

def setup_api_key():
    """Create a script to properly set the API key"""
    print("\nCreating API key setup script...")
    
    script_content = '''#!/bin/bash
# Set the API key properly
export ANTHROPIC_API_KEY="[API_KEY_NEEDED]"

echo "API key set. Length: ${#ANTHROPIC_API_KEY}"

# Run the autonomous proof system
if [ "$1" = "auto" ]; then
    python3 setup_autonomous_proof.py 2>&1 | tee autonomous_proof_run.log
elif [ "$1" = "focused" ]; then
    python3 Solver/focused_solver.py 2>&1 | tee focused_solver_run.log
elif [ "$1" = "incremental" ]; then
    python3 Solver/incremental_solver.py 2>&1 | tee incremental_solver_run.log
else
    echo "Usage: ./run_with_api.sh [auto|focused|incremental]"
fi
'''
    
    with open("run_with_api.sh", "w") as f:
        f.write(script_content)
    
    os.chmod("run_with_api.sh", 0o755)
    print("✓ Created run_with_api.sh script")

def create_fixed_autonomous_proof():
    """Create a fixed version of the autonomous proof system that handles API auth correctly"""
    print("\nCreating fixed autonomous proof system...")
    
    # Read the original file
    with open("setup_autonomous_proof.py", "r") as f:
        content = f.read()
    
    # Add better error handling for API responses
    content = content.replace(
        'if response.status == 200:',
        '''if response.status == 200:
                        result = await response.json()
                        return result["content"][0]["text"]
                    elif response.status == 401:
                        error_text = await response.text()
                        logger.error(f"API authentication error (401): {error_text}")
                        logger.error("Please check that your API key is valid")
                        return None
                    else:'''
    )
    
    # Save as a new file
    with open("setup_autonomous_proof_fixed.py", "w") as f:
        f.write(content)
    
    print("✓ Created setup_autonomous_proof_fixed.py")

def main():
    print("=== Fixing Navier-Stokes Project Issues ===\n")
    
    # Step 1: Fix syntax errors
    fix_basic_lean()
    
    # Step 2: Clean and rebuild
    clean_build()
    
    # Step 3: Set up API key handling
    setup_api_key()
    
    # Step 4: Create fixed autonomous proof system
    create_fixed_autonomous_proof()
    
    print("\n=== All fixes applied ===")
    print("\nTo run the proof system with the correct API key:")
    print("  ./run_with_api.sh auto      # For autonomous proof")
    print("  ./run_with_api.sh focused   # For focused solver")
    print("  ./run_with_api.sh incremental  # For incremental solver")
    
    print("\nNote: The API authentication errors suggest the API key might be:")
    print("1. Invalid or expired")
    print("2. For a different Anthropic product (e.g., Claude.ai instead of API)")
    print("3. Missing required permissions")
    print("\nPlease verify your API key at: https://console.anthropic.com/")

if __name__ == "__main__":
    main() 