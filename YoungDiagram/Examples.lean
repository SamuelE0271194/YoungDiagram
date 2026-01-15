import YoungDiagram.Gene
import YoungDiagram.Chromosome

#eval [true].isAlt
#eval [true, true].isAlt
#eval [true, false].isAlt
#eval [true, false, true].isAlt
#eval [false, true, false].isAlt

#eval [true].toGene
#eval [true, false].toGene
#eval [true, false, true].toGene
#eval [false, true, false].toGene

#eval [true].toGene.toList
#eval [true, false].toGene.toList
#eval [true, false, true].toGene.toList
#eval [false, true, false].toGene.toList

#eval [true].toGene.Signature
#eval [true, false].toGene.Signature
#eval [true, false, true].toGene.Signature
#eval [false, true, false].toGene.Signature

open Chromosome Pointwise

#check Pi
#check Mix (Lambda, Pi)
#check Mix (Pi, Lambda)
#check Mix (2 • Lambda, Pi)
#check Mix (Pi, 2 • Lambda)

#synth SMul ℕ variety
