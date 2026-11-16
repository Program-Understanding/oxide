'''
Author: Nate Buck
Last updated November 12th, 2026
'''
import logging
import ssl
import time
import os, httpx
from openai import OpenAI
from concurrent.futures import ThreadPoolExecutor
from openai import APIStatusError, APIConnectionError, RateLimitError


NAME = "agent_compare"
logger = logging.getLogger(NAME)

MODEL = "qwen3.8-27b"
MAX_ATTEMPTS = 10

def _ask (prompt):
    client = OpenAI (
        base_url="https://131.204.27.231/v1",
        api_key=os.environ["PUL_API_KEY"],
        http_client=httpx.Client(verify=ssl.create_default_context(cafile=os.path.expanduser("~/.pul/ca.crt")), timeout=600),
        max_retries=0,
    )
    error_occurred = False
    # Tries to connect to the LLM giving 10 tries just in case
    for attempt in range(MAX_ATTEMPTS):
        try:
            response = client.chat.completions.create(
                model=MODEL, 
                messages=[{"role": "user", "content": prompt}],
            )
            return response
        
        except APIConnectionError as e:
            logger.warning("Connection problem: %s", e.__cause__)
            error_occurred = True;
            
        except RateLimitError as e:
            logger.warning("Rate limited or out of quota: %s", e.message)
            error_occurred = True;
            
        except APIStatusError as e:
            if e.status_code < 500:
                raise # If error code is 400-404, it won't fix itself
            logger.warning(f"API returned {e.status_code}: {e.message}")
            error_occurred = True;
            
        except Exception as e:
            logger.warning(f"Unexpected error occured: {type(e).__name__}: {e}")
            error_occurred = True;
            raise
        if attempt < MAX_ATTEMPTS - 1:
            wait_time = 2 ** attempt
            if wait_time > 120:
                wait_time = 120
            logger.warning(f"Retrying in {wait_time} seconds")
            time.sleep(wait_time)
    
    raise RuntimeError(f"Request failed after {MAX_ATTEMPTS} attempts.")

            

def send_query (args, opts):
    '''
    This is a tool that lets you query LiteLLM using model qwen3.8-27b
    that uses the Oxide MCP server.

    Using 'run_query [prompt]' sends the query using the LiteLLM.

    **NOTE you MUST export your PUL API key for this plugin to work**
    '''
    from oxide.core import api

    # Must have at least a query to send
    if len(args) < 1:
        logger.critical("You must provide at least a query to send to LiteLLM.")
        return

    prompt = args[0]
    
    # Just query given
    response = _ask(prompt)
    # If you want all of the information the conversation gives including tokens, tool calls, etc.
    if 'verbose' in opts: 
        print(response.model_dump())
        return response.model_dump()
    print(response.choices[0].message.content)
    return response.choices[0].message.content
    

exports = [send_query]