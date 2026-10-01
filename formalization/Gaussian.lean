import Gaussian.Physical.Boson.GaussianClassification
import Gaussian.Physical.Boson.ThermalProductDensity
import Gaussian.Physical.Boson.WeylUncertainty
import Gaussian.Physical.Boson.CovarianceGeometry
import Gaussian.Physical.Boson.FourierAction
import Gaussian.Physical.Boson.WeylComposition
import Gaussian.Physical.Boson.ChirpAction
import Gaussian.Physical.Boson.ConfigurationSymplectic
import Gaussian.Physical.Boson.VectorFamilyDensity
import Gaussian.Physical.Boson.ProductWeyl
import Gaussian.Physical.Boson.SchrodingerNontrivial
import Gaussian.Analysis.HilbertBasisParseval
import Gaussian.Algebra.SymplecticPivot
import Gaussian.Phase.BosonicPurificationSelection
import Gaussian.Phase.BosonicPurificationLift
import Gaussian.Phase.BosonicPurificationCostTransport
import Gaussian.Phase.BosonicPurificationProduct
import Gaussian.Physical.Boson.ProductCompleteness
import Gaussian.Phase.BosonicPurificationPadding
import Gaussian.Physical.Fermion.GlobalMinimum
import Gaussian.Negative.SuppliedFermionMixedDeletion
import Gaussian.Physical.Fermion.CountedCutSelection
import Gaussian.Physical.Fermion.FiniteTotalPadding
import Gaussian.Physical.Fermion.FiniteTotalDeletion
import Gaussian.Physical.Fermion.FinitePartySwap
import Gaussian.Physical.Fermion.FinitePointTransport
import Gaussian.Physical.Fermion.DefiniteParity
import Gaussian.Physical.Fermion.GeneralFactorization
import Gaussian.Optimization.MatchedIteration
import Gaussian.Physical.Boson.ProbabilityMixture
import Gaussian.Physical.Boson.GaussianParameters
import Gaussian.Spectral.HermitianDirectSum
import Gaussian.Negative.EntropyAndAttainment
import Gaussian.Negative.SymplecticComplement
import Gaussian.Negative.UnsignedSwap
import Gaussian.Negative.NonuniqueSelection
import Gaussian.Physical.Fermion.Purification
import Gaussian.Physical.Boson.MeanRemoval
import Gaussian.Physical.Boson.PureEntropy
import Gaussian.Physical.Boson.VacuumCharacteristic
import Gaussian.Spectral.WilliamsonCoefficients
import Gaussian.Optimization.FiniteDescent
import Gaussian.Covariance.Uncertainty
import Gaussian.Phase.Restriction
import Gaussian.Phase.Williamson
import Gaussian.Entropy.Compression
import Gaussian.Attainment.BosonicCuts
import Gaussian.Physical.Fermion.PairedCovariance
import Gaussian.Physical.Fermion.ThermalPurity
import Gaussian.Physical.Fermion.Circuit
import Gaussian.Physical.Fermion.LocalAction
import Gaussian.Physical.Fermion.Factorization
import Gaussian.Physical.Boson.GaussianPredicate
import Gaussian.Physical.Boson.DiagonalEntropy
import Gaussian.Spectral.HermitianEigenbasis

import Gaussian.Physical.Boson.GlobalMinimum
import Gaussian.Physical.Boson.PureProductFactorization
import Gaussian.Physical.Boson.GaussianFactorization
import Gaussian.Negative.FermionEntropyGap

/-! Actual finite-mode bosonic and fermionic Gaussian minimum purification.
Both sector roots supply matched witnesses attaining the all-finite objective.
Source-level semantic, trust, mutation and fresh-rebuild audits are recorded
separately from this mathematical integration module. -/
