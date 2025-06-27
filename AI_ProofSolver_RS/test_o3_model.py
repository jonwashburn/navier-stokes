#!/usr/bin/env python3
"""Test if o3 model is available through OpenAI API"""

import sys
from openai import OpenAI

def test_o3_availability(api_key):
    client = OpenAI(api_key=api_key)
    
    try:
        # Try to list models
        print("Checking available models...")
        models = client.models.list()
        
        print("\nModels containing 'o3':")
        o3_models = [m for m in models if 'o3' in m.id.lower()]
        for model in o3_models:
            print(f"  - {model.id}")
            
        if not o3_models:
            print("  No o3 models found")
            
        print("\nAll available models:")
        for model in sorted([m.id for m in models]):
            print(f"  - {model}")
            
        # Try to use o3 directly
        print("\nTesting o3 model directly...")
        response = client.chat.completions.create(
            model="o3",
            messages=[{"role": "user", "content": "Say 'Hello'"}],
            max_tokens=10
        )
        print("✓ o3 model is available and working!")
        
    except Exception as e:
        print(f"\n✗ Error: {e}")
        print(f"Error type: {type(e).__name__}")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        api_key = sys.argv[1]
    else:
        print("Please provide API key as argument")
        sys.exit(1)
        
    test_o3_availability(api_key) 