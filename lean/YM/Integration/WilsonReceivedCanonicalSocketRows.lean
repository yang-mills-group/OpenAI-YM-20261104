import YM.Integration.WilsonReceivedCanonicalVerseBasis
import YM.Integration.WilsonOriginalThermometerRealPalette
import YM.Integration.WilsonOriginalThermometerGradedPalette

/-! The three chosen raw sockets, before their external physical coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketRows
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Push Push.AbsoluteSums
open Earn Sunrise QuadraticLocal.Affinity XSpace PhysicalNext.Repeat.Legato
open WilsonOriginalThermometerPalette WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3 → ℕ)(q:(j:Fin 3) → Choice R d j)
local notation "i₀" j:max => entry R d j (q j)
local notation "u₀" j:max => raw R d (i₀ j)

def loan (hd:∀j,d j ≤ levels j)(j:Fin 3):Loan where
  e:=rank R d (i₀ j)-pole R d (i₀ j)
  r:=rank R d (i₀ j)
  toll:=levels j
  higher:=WilsonOriginalThermometerGradedPalette.positive j
  crest:=by
    have bound:=(WilsonOriginalStarGradedScene.pole_grade R d (i₀ j))
    rw [site] at bound
    have price:=hd j
    have live:=low R d (i₀ j)
    omega

variable (hd:∀j,d j ≤ levels j){n:Side}(o:Fin 3 → Site n)(σ:ℝ)

def row (j:Fin 3):Row (Passport.point o) (Stock.census (Fin 3)) G (Wallet disks) where
  binder:=WilsonOriginalStarSceneRows.binder o j
  lamp:=loan R d q hd j
  atom:=unitAtom (u₀ j) σ
  clear:=constant R d (i₀ j)
  lawful:=invariant _ _ (lawful R d (i₀ j))
  salary:=1+normalizer (u₀ j) σ
  sound:=by linarith [positive (u₀ j) σ]
  paint x:=((normalizer (u₀ j) σ:ℝ):ℂ)*probe j x
  rank:=clear R d (i₀ j)

local notation "M" => row R d q hd o σ

theorem tested:Tableau (fun _:Fin 3=> (⊥:Submodule ℝ ℂ)) disks M:=by
  refine ⟨fun j=>?_⟩
  exact (WilsonOriginalThermometerRealPalette.attentive j).linear (LinearMap.mul ℝ ℂ (normalizer (u₀ j) σ:ℂ))

def price (j:Fin 3)(c:Choice R d j):ℝ:=
  let a:=raw R d (entry R d j c)
  (1+normalizer a σ)*Real.exp (σ*a.length)

def charge (w:Fin 3 → ℝ):ℝ:=∑j,w j*price R d σ j (q j)

theorem nonneg (j:Fin 3)(c:Choice R d j):0 ≤ price R d σ j c:=
  mul_nonneg (add_nonneg zero_le_one (positive _ _).le) (Real.exp_nonneg _)

theorem fleet (w:Fin 3→ℝ)(weight:∀j,0<w j)(order seats shelf:ℕ)
    (fit:∀j,rank R d (i₀ j) ≤ order)(three:3 ≤ seats)(room:14 ≤ shelf):
    Scene.Armada M w levels σ (charge R d q σ w) order seats shelf:=by
  refine ⟨⟨fun s=>s.val.card_le_univ.trans (by simpa using three),
    fun s=>(sum_le_sum_of_subset (subset_univ s.val)).trans
      (WilsonOriginalThermometerGradedPalette.total.le.trans room)⟩,weight,?_,?_,?_⟩
  · intro y
    have h (j:Fin 3):0≤w j*price R d σ j (q j):=mul_nonneg (weight j).le (nonneg ..)
    have booked (j:Fin 3):Poly.toll w (M j).mode * (M j).height σ=w j*price R d σ j (q j):=by
      change (∏ v∈({j}:Finset (Fin 3)),w v)*(_*Real.exp (σ*↑((WilsonOriginalStarSceneRows.binder o j).length+(u₀ j).length)))=_
      simp [WilsonOriginalStarSceneRows.length,price,row]
    refine ⟨fun j=>?_,(hasSum_fintype _).summable,?_⟩
    · change 0 ≤ if (M j).center=y then Poly.toll w (M j).mode*(M j).height σ else 0
      split
      · rw [booked];exact h _
      · exact le_rfl
    · rw [tsum_fintype]
      apply sum_le_sum
      intro j _
      split
      · exact (booked j).le
      · exact h _
  · refine ⟨fun _=>unitPrice _ _,fun j=>⟨?_,?_⟩⟩
    · exact (Nat.sub_le _ _).trans (fit j)
    · change levels j=∑v∈({j}:Finset (Fin 3)),levels v
      simp
  · intro j x
    change ‖((normalizer (u₀ j) σ:ℝ):ℂ)*probe j x‖≤1+_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive _ _)]
    exact (mul_le_of_le_one_right (positive _ _).le (x j).property).trans (le_add_of_nonneg_left zero_le_one)

def ceiling:ℝ:=∑j,∑c:Choice R d j,price R d σ j c

theorem one:charge R d q σ (fun _=>1) ≤ ceiling R d σ:=by
  simp only [charge,one_mul,ceiling]
  exact sum_le_sum (fun j _=>single_le_sum (fun c _=>nonneg R d σ j c) (mem_univ (q j)))

theorem nominal {h:Fin 3→ℕ}(κ:(j:Fin 3)→Knob (h j))(pt:Fin 3→Chamber)
    (j:Fin 3)(g:ℝ)(x:Wallet disks)(U:Config G n):
    (M j).nominal g x U=probe j x*WilsonReceivedCanonicalVerseBasis.restored R d κ pt g j (q j) (o j) U:=by
  let a:=u₀ j
  let z:=normalizer a σ
  have lag:(loan R d q hd j).lag=-(pole R d (i₀ j):ℤ):=by
    change ((rank R d _-pole R d _:ℕ):ℤ)-rank R d _=_
    have enough:=low R d (i₀ j)
    omega
  change ((z:ℂ)*probe j x)*↑(g^(loan R d q hd j).lag*(unitAtom a σ).unmasked U (o j))=_
  rw [lag,show (unitAtom a σ).unmasked U (o j)=z⁻¹*a.unmasked U (o j) from evaluated a σ _,Complex.ofReal_mul,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_zpow]
  unfold WilsonReceivedCanonicalVerseBasis.restored
  dsimp only
  rw [WilsonReceivedCanonicalVerseBasis.field]
  have cancel:(z:ℂ)*(z:ℂ)⁻¹=1:=mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive a σ).ne')
  change _=probe j x*((g:ℂ)^(-(pole R d (i₀ j):ℤ))*↑(a.unmasked U (o j)))
  linear_combination probe j x*(g:ℂ)^(-(pole R d (i₀ j):ℤ))*↑(a.unmasked U (o j))*cancel

end YM.Integration.WilsonReceivedCanonicalSocketRows
