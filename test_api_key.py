#!/usr/bin/env python3
"""Test API key authentication"""

import os
import asyncio
import aiohttp
import json

async def test_api_key():
    # Try different ways of setting the API key
    api_keys_to_test = [
        # From environment
        os.environ.get("ANTHROPIC_API_KEY"),
        # Direct key
        "[API_KEY_NEEDED]"
    ]
    
    for i, api_key in enumerate(api_keys_to_test):
        if not api_key:
            print(f"Test {i+1}: No API key")
            continue
            
        print(f"\nTest {i+1}:")
        print(f"API key length: {len(api_key)}")
        print(f"API key prefix: {api_key[:15]}...")
        print(f"API key suffix: ...{api_key[-10:]}")
        
        # Test with Claude API
        headers = {
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
            "content-type": "application/json"
        }
        
        data = {
            "model": "claude-3-5-sonnet-20241022",
            "max_tokens": 100,
            "messages": [{"role": "user", "content": "Say 'API key works!'"}]
        }
        
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    "https://api.anthropic.com/v1/messages",
                    headers=headers,
                    json=data
                ) as response:
                    print(f"Response status: {response.status}")
                    if response.status == 200:
                        result = await response.json()
                        print(f"✓ Success! Response: {result['content'][0]['text']}")
                    else:
                        error_text = await response.text()
                        print(f"✗ Error: {error_text}")
        except Exception as e:
            print(f"✗ Exception: {e}")

if __name__ == "__main__":
    print("=== Testing API Key Authentication ===")
    asyncio.run(test_api_key()) 