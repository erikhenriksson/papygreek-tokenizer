from setuptools import setup

setup(
    name="papygreektokenizer",
    version="0.1",
    url="https://github.com/erikhenriksson/papygreek-tokenizer",
    author="Erik Henriksson",
    author_email="erik.ilmari.henriksson@gmail.com",
    description="A tokenizer for PapyGreek texts",
    packages=["papygreektokenizer"],
    install_requires=["regex", "lxml", "python-dotenv"],
    zip_safe=False,
)
