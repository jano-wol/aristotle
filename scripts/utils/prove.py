import asyncio
import aristotlelib
import logging

from utils import load_api_key

# Load and set API key
aristotlelib.set_api_key(load_api_key())

logging.basicConfig(
    level=logging.INFO,
    format="%(levelname)s - %(name)s - %(message)s"
)

async def main():
    # Prove a theorem from a Lean file
    solution_path = await aristotlelib.Project.prove_from_file("/home/jw/Repositories/aristotle/projects/komal.lean")
    print(f"Solution saved to: {solution_path}")

asyncio.run(main())
