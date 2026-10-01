import Gaussian.Analysis.GaussianGramLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section
namespace Gaussian.Analysis

def complexGramScalar (a b c d : ℝ) : ℂ :=
  (2-(Real.exp (-a/4):ℂ)-(Real.exp (-a/4):ℂ))+
  (2-(Real.exp (-b/4):ℂ)-(Real.exp (-b/4):ℂ))+
  Complex.I*(Complex.exp (-(d:ℂ)/4-(c:ℂ)/2*Complex.I)-
    (Real.exp (-a/4):ℂ)-(Real.exp (-b/4):ℂ)+1)-
  Complex.I*(Complex.exp (-(d:ℂ)/4+(c:ℂ)/2*Complex.I)-
    (Real.exp (-b/4):ℂ)-(Real.exp (-a/4):ℂ)+1)

theorem complexGramScalar_re (a b c d : ℝ) :
    (complexGramScalar a b c d).re=gramProfile a b c d 1 := by
  simp [complexGramScalar,gramProfile,Complex.mul_re,Complex.exp_im,Complex.exp_re]
  ring

theorem gramProfile_scale (a b c d t : ℝ) :
    gramProfile (t*(t*a)) (t*(t*b)) (t*(t*c)) (t*(t*d)) 1=
      gramProfile a b c d (t^2) := by
  have ha : -(t*(t*a))/4= -a*t^2/4 := by ring
  have hb : -(t*(t*b))/4= -b*t^2/4 := by ring
  have hc : (t*(t*c))/2=c*t^2/2 := by ring
  have hd : -(t*(t*d))/4= -d*t^2/4 := by ring
  simp only [gramProfile,mul_one,ha,hb,hc,hd]

end Gaussian.Analysis
