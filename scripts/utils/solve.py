import asyncio
import aristotlelib
import logging
from pathlib import Path
from datetime import datetime

from utils import load_api_key

# Load and set API key
aristotlelib.set_api_key(load_api_key())

logging.basicConfig(
    level=logging.INFO,
    format="%(levelname)s - %(name)s - %(message)s"
)

def list_problems():
    """List all available problem files in the problems directory."""
    # Get the problems directory (assuming script is in scripts/utils/)
    script_dir = Path(__file__).parent
    problems_dir = script_dir.parent.parent / "problems"

    if not problems_dir.exists():
        print(f"Error: Problems directory not found at {problems_dir}")
        return []

    # Find all .lean files
    lean_files = sorted(problems_dir.glob("*.lean"))

    if not lean_files:
        print("No problem files found in problems/ directory")
        return []

    return lean_files

async def main():
    # List available problems
    problems = list_problems()

    if not problems:
        return

    print("Available problems:")
    print()
    for i, problem in enumerate(problems, 1):
        print(f"  {i}. {problem.stem}")
    print()

    # Ask user which problem to solve
    while True:
        choice = input("Which problem would you like to solve? (enter number or name): ").strip()

        # Try to parse as number
        if choice.isdigit():
            idx = int(choice) - 1
            if 0 <= idx < len(problems):
                selected_problem = problems[idx]
                break
            else:
                print(f"Invalid number. Please choose between 1 and {len(problems)}")
                continue

        # Try to match by name
        matching = [p for p in problems if p.stem == choice]
        if matching:
            selected_problem = matching[0]
            break

        # Try partial match
        matching = [p for p in problems if choice.lower() in p.stem.lower()]
        if len(matching) == 1:
            selected_problem = matching[0]
            break
        elif len(matching) > 1:
            print(f"Ambiguous choice. Did you mean: {', '.join(p.stem for p in matching)}?")
            continue

        print(f"Problem '{choice}' not found. Please try again.")

    print()
    print(f"Solving: {selected_problem.stem}")
    print()

    # Prepare solution path in solutions/ directory
    script_dir = Path(__file__).parent
    solutions_dir = script_dir.parent.parent / "solutions"

    # Create solutions directory if it doesn't exist
    solutions_dir.mkdir(exist_ok=True)

    # Create a filename based on problem name and timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    solution_file = solutions_dir / f"{selected_problem.stem}_{timestamp}.lean"

    # Solve the selected problem and save directly to the specified path
    await aristotlelib.Project.prove_from_file(str(selected_problem), output_file_path=str(solution_file))
    print()
    print(f"Solution saved to: {solution_file}")

asyncio.run(main())
