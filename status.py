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

async def list_projects():
    projects, pagination_key = await aristotlelib.Project.list_projects(limit=10)

    for project in projects:
        print(f"Project {project.project_id}: {project.status}")

    # Get next page if available
    if pagination_key:
        more_projects, pagination_key = await aristotlelib.Project.list_projects(pagination_key=pagination_key)
        print(f"Found {len(more_projects)} more projects")

asyncio.run(list_projects())
