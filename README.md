# Lean Tutorial @ CHANGE Seminar

This repository contains the resources for the Lean tutorial session of my talk *An Invitation to Blueprint-Driven Formalisation of Mathematical Research in Lean* presented at the weekly research seminar on CHallenges in ANalysis and GEometry ([CHANGE](https://mbschulz.github.io/change_seminar)) at the University of Trento on February 11, 2025.

[![CHANGE](images/logo.png)](https://r1.unitn.it/change/)

## Installing VS Code

VS Code is the recommended IDE for working with Lean 4. To install VS Code, follow these steps:

1. Visit the official VS Code [website](https://code.visualstudio.com).
2. Download the latest version of VS Code for your operating system (Windows, macOS, or Linux).
3. Follow the installation instructions provided on the website to complete the setup process.

Once the installation is complete, you can proceed with configuring VS Code for Lean 4 development.

## Installing Lean 4

To install Lean 4, please follow these instructions:

1. **Install the Lean 4 Extension in VS Code**:
   - Open VS Code.
   - Navigate to the *Extensions* sidebar by clicking on the square icon on the left panel.
   - Search for *Lean 4* in the search bar and install the `Lean 4` extension.

   ![Installing the vscode-lean4 extension](images/code-ext.png)

2. **Access the Lean 4 Setup Guide**:
   - Create a new text file by selecting *File > New Text File* or using the keyboard shortcut (`Ctrl + N` on Windows/Linux or `Cmd + N` on macOS).
   - Click on the $\forall$-symbol located in the top right corner of the window.
   - From the dropdown menu, select *Documentation… > Docs: Show Setup Guide*.

   ![Docs: Show Setup Guide](images/show-setup-guide.png)

3. **Follow the Instructions in the Setup Guide**:
   - Carefully read and follow the instructions provided in the Lean 4 setup guide to complete the installation process.

   ![Setup Guide](images/setup_guide.png)

## Cloning this Repository

To clone this repository, run the following command:

```bash
git clone https://github.com/pitmonticone/LeanCHANGE.git
```

For detailed instructions, please refer to the [GitHub documentation](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository)
on cloning repositories.

After successfully cloning the repository, navigate into the project directory and
execute the following command to retrieve the necessary cached dependencies:

```
cd LeanCHANGE/
lake exe cache get
```

## Search Engines

- [Lean Package Registry](https://reservoir.lean-lang.org)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Loogle](https://loogle.lean-lang.org)
- [Moogle](https://moogle.ai)
- [LeanSearch](https://leansearch.net)
- [Zulip Channel "Is There Code for X?"](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F)

## References

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/title_page.html)
- [Glimpse Of Lean](https://github.com/PatrickMassot/GlimpseOfLean)
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)
- [Lean 4 Tactics Cheatsheet](lean-tactics.pdf)

![Institutions](images/institutions.png)
