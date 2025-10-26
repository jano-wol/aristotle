import asyncio
import aristotlelib
import logging
import sys
from pathlib import Path

from utils import load_api_key

# Load and set API key
aristotlelib.set_api_key(load_api_key())

logging.basicConfig(
    level=logging.INFO,
    format="%(levelname)s - %(name)s - %(message)s"
)

async def list_all_projects():
    """List all available projects with pagination."""
    all_projects = []
    pagination_key = None

    while True:
        projects, pagination_key = await aristotlelib.Project.list_projects(
            limit=100,
            pagination_key=pagination_key
        )
        all_projects.extend(projects)

        if not pagination_key:
            break

    return all_projects

async def get_project_by_id(project_id):
    """Get a project by its ID."""
    try:
        project = await aristotlelib.Project.from_id(project_id)
        return project
    except Exception as e:
        print(f"Error: Could not load project with ID '{project_id}': {e}", file=sys.stderr)
        return None

async def main():
    # Check if a project ID was provided as a command-line argument
    if len(sys.argv) > 1:
        project_id = sys.argv[1]
        print(f"Loading project: {project_id}")
        print()

        project = await get_project_by_id(project_id)
        if not project:
            sys.exit(1)
    else:
        # List all projects
        print("Fetching projects...")
        projects = await list_all_projects()

        if not projects:
            print("No projects found.")
            return

        # Filter to only show COMPLETE projects
        complete_projects = [p for p in projects if p.status == aristotlelib.ProjectStatus.COMPLETE]

        print()
        print(f"Found {len(projects)} total projects, {len(complete_projects)} completed.")
        print()
        print("Completed projects:")
        print()

        if not complete_projects:
            print("  No completed projects found.")
            print()
            print("Showing all projects:")
            print()
            for i, p in enumerate(projects, 1):
                print(f"  {i}. {p.project_id} - {p.status}")
            print()
            print("Note: Solutions are only available for COMPLETE projects.")
            return

        for i, p in enumerate(complete_projects, 1):
            print(f"  {i}. {p.project_id}")
        print()

        # Ask user which project to get solution for
        while True:
            choice = input("Which project would you like to get the solution for? (enter number or project ID): ").strip()

            # Try to parse as number
            if choice.isdigit():
                idx = int(choice) - 1
                if 0 <= idx < len(complete_projects):
                    project = complete_projects[idx]
                    break
                else:
                    print(f"Invalid number. Please choose between 1 and {len(complete_projects)}")
                    continue

            # Try to match by exact project ID
            matching = [p for p in complete_projects if p.project_id == choice]
            if matching:
                project = matching[0]
                break

            # Try partial match
            matching = [p for p in complete_projects if choice.lower() in p.project_id.lower()]
            if len(matching) == 1:
                project = matching[0]
                break
            elif len(matching) > 1:
                print(f"Ambiguous choice. Did you mean: {', '.join(p.project_id for p in matching)}?")
                continue

            print(f"Project '{choice}' not found in completed projects. Please try again.")

    # Check if project is COMPLETE
    if project.status != aristotlelib.ProjectStatus.COMPLETE:
        print()
        print(f"Error: Project {project.project_id} status is {project.status}")
        print("Solutions are only available for COMPLETE projects.")
        sys.exit(1)

    print()
    print(f"Getting solution for project: {project.project_id}")
    print()

    # Prepare solution path in solutions/ directory
    script_dir = Path(__file__).parent
    solutions_dir = script_dir.parent.parent / "solutions"

    # Create solutions directory if it doesn't exist
    solutions_dir.mkdir(exist_ok=True)

    # Create a filename based on project ID
    solution_file = solutions_dir / f"{project.project_id}.lean"

    # Get the solution and save directly to the specified path
    try:
        await project.get_solution(output_path=str(solution_file))
    except Exception as e:
        print(f"Error: Failed to retrieve solution: {e}", file=sys.stderr)
        sys.exit(1)

    print(f"Solution saved to: {solution_file}")

asyncio.run(main())
