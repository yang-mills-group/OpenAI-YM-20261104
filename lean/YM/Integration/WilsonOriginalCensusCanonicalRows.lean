import YM.Integration.WilsonReceivedCanonicalVerseBasis
import YM.Integration.WilsonOriginalStarGradedScene
import YM.Integration.WilsonOriginalMixedBlockRows

/-! A single literal canonical socket per originally planted physical name. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalRows
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Push Push.AbsoluteSums
open Earn Sunrise QuadraticLocal.Affinity XSpace PhysicalNext.Repeat.Legato
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords WilsonOriginalMixedBlockRows
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open scoped Classical BigOperators
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V → ℕ)(q:(j:V) → Choice R d j)

def probe (j:V)(x:Wallet (room V)):ℂ:=(x j).val

omit [Fintype V] in
theorem attentive (j:V):Attn (fun _:V=>(⊥:Submodule ℝ ℂ)) (room V) {j} (probe j):=by
  refine ⟨fun x y eq=>congrArg Subtype.val (eq j (mem_singleton_self _)),?_,?_⟩
  · intro i hi x s t u a b hu
    obtain rfl:=mem_singleton.mp hi
    simpa only [probe,Function.update_self] using hu
  · intro i hi x hx
    obtain rfl:=mem_singleton.mp hi
    exact (Submodule.mem_bot ℝ).mp hx
local notation "i₀" j:max => entry R d j (q j)
local notation "u₀" j:max => raw R d (i₀ j)

def loan (hd:∀j,0 < d j)(j:V):Loan where
  e:=rank R d (i₀ j)-pole R d (i₀ j)
  r:=rank R d (i₀ j)
  toll:=d j
  higher:=hd j
  crest:=by
    have bound:=(WilsonOriginalStarGradedScene.pole_grade R d (i₀ j))
    rw [site] at bound
    have live:=low R d (i₀ j)
    omega

variable (hd:∀j,0 < d j){n:Side}(o:V → Site n)(σ:ℝ)

def row (j:V):Row (Passport.point o) (Stock.census V) G (Wallet (room V)) where
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

theorem tested:Tableau (fun _:V=> (⊥:Submodule ℝ ℂ)) (room V) M:=by
  refine ⟨fun j=>?_⟩
  exact (attentive j).linear (LinearMap.mul ℝ ℂ (normalizer (u₀ j) σ:ℂ))

def price (j:V)(c:Choice R d j):ℝ:=
  let a:=raw R d (entry R d j c)
  (1+normalizer a σ)*Real.exp (σ*a.length)

def charge (w:V → ℝ):ℝ:=∑j,w j*price R d σ j (q j)

omit [Fintype V] [DecidableEq V] in
theorem nonneg (j:V)(c:Choice R d j):0 ≤ price R d σ j c:=
  mul_nonneg (add_nonneg zero_le_one (positive _ _).le) (Real.exp_nonneg _)

theorem fleet (w:V→ℝ)(weight:∀j,0<w j)(order seats shelf:ℕ)
    (fit:∀j,rank R d (i₀ j) ≤ order)(slots:Fintype.card V ≤ seats)(space:∑j,d j ≤ shelf):
    Scene.Armada M w d σ (charge R d q σ w) order seats shelf:=by
  refine ⟨⟨fun s=>s.val.card_le_univ.trans slots,
    fun s=>(sum_le_sum_of_subset (subset_univ s.val)).trans
      space⟩,weight,?_,?_,?_⟩
  · intro y
    have h (j:V):0≤w j*price R d σ j (q j):=mul_nonneg (weight j).le (nonneg ..)
    have booked (j:V):Poly.toll w (M j).mode * (M j).height σ=w j*price R d σ j (q j):=by
      change (∏ v∈({j}:Finset V),w v)*(_*Real.exp (σ*↑((WilsonOriginalStarSceneRows.binder o j).length+(u₀ j).length)))=_
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
    · change d j=∑v∈({j}:Finset V),d v
      simp
  · intro j x
    change ‖((normalizer (u₀ j) σ:ℝ):ℂ)*probe j x‖≤1+_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive _ _)]
    exact (mul_le_of_le_one_right (positive _ _).le (x j).property).trans (le_add_of_nonneg_left zero_le_one)

def ceiling:ℝ:=∑j,∑c:Choice R d j,price R d σ j c

omit [DecidableEq V] in
theorem one:charge R d q σ (fun _=>1) ≤ ceiling R d σ:=by
  simp only [charge,one_mul,ceiling]
  exact sum_le_sum (fun j _=>single_le_sum (fun c _=>nonneg R d σ j c) (mem_univ (q j)))

theorem nominal {h:V→ℕ}(κ:(j:V)→Knob (h j))(pt:V→Chamber)
    (j:V)(g:ℝ)(x:Wallet (room V))(U:Config G n):
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

end YM.Integration.WilsonOriginalCensusCanonicalRows
