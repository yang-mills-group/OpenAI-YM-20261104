import YM.PertExtension.ScreenGeometry
import YM.PertExtension.SelfRate

/-! The two distinct roles of self and off-diagonal top contractions, for
 sequences of separated mark samples. `prize` uses *no* same-mark
contractions; this isn't an equality with the joint orbit pairing.
 -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection Normal Converter Screens
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal RealInnerProductSpace FourierTransform
variable {G : Gauge}(q : ℕ+)
variable {n : ℕ}

def jointKernel (sites:Fin n→Cover) (k:ℕ):Symmetric (Fin n × Atom G) where
   cov i j := ((echo (side q k) (sites i.1) (sites j.1) (atAddress i.2) (atAddress j.2):ℝ):ℂ)
   symm i j := congr_arg Complex.ofReal (echo_comm (side_even q k) ..)

def extractSelf (K:Symmetric (Fin n × Atom G)):Symmetric (Fin n × Atom G) where
   cov i j:=if i.1 = j.1 then K.cov i j else 0
   symm i j:=by split_ifs with h h₂ h₂; exact K.symm ..;exact (h₂ h.symm).elim;exact (h h₂.symm).elim;rfl

def crossKernel (U:ℕ→ Fin n→ Cover)(k:ℕ):Symmetric (Fin n×Atom G):= prize atAddress (pathSimple G q U k) (fun i j x y=>by
    unfold pathSimple; split_ifs with h h₂ h₂;rfl;exact (h₂ h.symm).elim;exact (h h₂.symm).elim;exact echo_comm (side_even ..) ..)
lemma decomposed (sites:ℕ→Fin n→Cover)(k):let K:=jointKernel (G:=G) q (sites k) k;let S:=extractSelf K
   K=S+crossKernel q sites k:=by
   intro K S; apply Symmetric.ext; funext i j
   by_cases h : i.1=j.1 <;>
     change _=(if i.1=j.1 then K.cov i j else 0)+ ↑((if _ then (0:Bridge G) else echo _ _ _) _ _)
   · simp [h]
   simp [h,K,jointKernel] -- adjust Beamer name


variable {q}(hq:1<q.val)
variable {U: Fin n→ℕ→Cover}{O:ℕ→Cover}(hO:Placement q O)
variable {x:Points n}(hx:x∈conf n)(hU:∀ i,Tendsto (fun k=>epsilon q k • mapZ (U i k)) atTop (𝓝 (x i)))
local notation "reg" => (Filter.atTop : Filter ℕ)

include hq hO hU hx
theorem ready : PathReady x q (fun t j=>withOrigin O (U j) t) := fun i j h=>by
   refine ⟨?_,1/8, by norm_num,fun f e b=> sheltered hq O hO (hU i) (hU j) e b f⟩
   convert! ((hU i).sub (hU j)) using 2; expose_names; dsimp only;rw [withOrigin,withOrigin, add_sub_add_left_eq_sub,Wall.sends_sub,smul_sub] -- adjust

omit hO hq hU hx
lemma direct_offset (A:Cover)(k:ℕ)(p s:Atom G) : direct G (side q k) A A (atAddress p) (atAddress s)=selfFull q p s k :=by
   unfold selfFull
   let a := basic G p.1.plaq p.2
   let b:=basic G s.1.plaq s.2
   let n':=side q k; let F(u:E4):=(stepsP (shell a b) n' 2 u).re
   have hv (c:Cover): direct G n' c c (atAddress p) (atAddress s)=F (captured c c p.1.offset s.1.offset):= direct_price a b n' c c _ _
   have hw (x' y'): captured A A x' y'=captured 0 0 x' y':=by unfold captured;rw [add_sub_add_left_eq_sub,zero_add,zero_add]
   rw [hv A,hv 0,hw]
include hO hq hU
lemma image_zone (a b: Atom G) (d : ℕ)(i : Fin n) :
    Tendsto (fun t=> (magnify q t)^d • ((↑(echo (side q t) (withOrigin O (U i) t) (withOrigin O (U i) t) (atAddress a) (atAddress b):ℝ):ℂ)-(covarianceSymbol G).cov a b)) atTop (𝓝 0) :=by
   let V:=withOrigin O (U i)
   let v(k):ℝ:=reflected G (side q k) (V k) (V k) (atAddress a) (atAddress b)
   have hS:=sheltered hq O hO (hU i) (hU i) a.1.offset b.1.offset a.1.plaq
   have hL:=far_ref_item hq (atAddress a) (atAddress b) d (by norm_num : 0<(1/8:ℝ)) hS
   have hp:Tendsto (fun t=> ↑(magnify q t^d*v t)) atTop (𝓝 (↑(0:ℝ):ℂ)):= Complex.continuous_ofReal.continuousAt.tendsto.comp hL
   have he: (↑(0:ℝ):ℂ)=0:=rfl
   replace hp: Tendsto (fun t=> magnify q t^d • (↑(v t):ℂ)) atTop (𝓝 (0:ℂ)):=by simpa only [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_eq_mul,Complex.ofReal_mul,he] using! hp
   rw [show (𝓝 (0:ℂ))=nhds (0+(↑(0:ℝ):ℂ)) from by simp]
   apply ((therm a b hq d).add hp).congr
   intro t; rw [← smul_add];congr 1;change (↑(selfFull _ _ _ t) : ℂ)- _ + ↑(v t)= ↑(direct G (side q t) (V t) (V t) (atAddress a) (atAddress b)+ v t:ℝ)-_
   rw [direct_offset,Complex.ofReal_add];abel

variable (d : ℕ)
include hx
set_option linter.unusedSectionVars false in
theorem gaussian_scaling_low (i j : Configuration.KeyIn G d)(s t:Fin n)(hst:s≠t):
   let V t j:=withOrigin O (U j) t
   let X t:= lifted d V atAddress (q:=q) t
   (∀ t,scope (perSlot (fun _ : Fin n=> features d atAddress (magnify q t))) (X t)=crossKernel q V t) ∧
      Tendsto (fun k=>(X k).cov (s,.inl i) (t,.inl j)) atTop (𝓝 ((currentX hx G d).cov (s,i) (t,j))) := by
   intro V X;refine ⟨fun t=>by apply shaped;exact pow_pos (by positivity) _,?_⟩
   exact lift_low d hx V hq (ready hq hO hx hU) _ s t hst i j
end YM.PertExtension.LatticePT
