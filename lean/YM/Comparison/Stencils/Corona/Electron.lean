import YM.Comparison.Stencils.Corona.Ribbon
import YM.PertExtension.SelfRate
/-!
# Line pair covariance at top

At finite even top side one must add the inversion image for actual
expectations; here prove calibration works on cover symbols and uses
exact infinite-volume Wilson curl symbol, with even-side limit independent
per slot; no uniform claim with growing supports. Use finite ordinary
(not inversion skew) positive-link algebra for congruence validation.
Build (only as a TOOL) a lifting to potential covariance--don't assume a
harmonic convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Corona
open Function Filter Finset MvPolynomial Lattice
open Next Next.Rank Next.Rank.Normal
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Projection
open scoped BigOperators Topology ContDiff Classical
variable {G : Gauge} {s : Signed} {n : Side} {α : Type*}

abbrev Crumb (G : Gauge):= Atom G
abbrev Tally (a:RG.Slot): Face ℤ := (a.offset,a.plaq)
abbrev Affiche (n: Side) (G : Gauge):=Face (Per n) × G.ColorIndex
abbrev Panel (n:Side)(G:Gauge):= Edge (Site n) × G.ColorIndex

def pul (p:RG.Slot):Face (Per n):= (wrap n p.offset,p.plaq)
def aliasFor (p: Crumb G): Affiche n G:=(pul p.1,p.2)

/-- Same convention used for each tone, not dividing by 2 a second time. -/
def full (n:Side) (G : Gauge): Symmetric (Crumb G) where
  cov p q := if p.2=q.2 then (↑(price (pul (n:=n) p.1) (pul q.1)):ℂ) else 0
  symm p q:=by by_cases h:p.2=q.2
               · rw [if_pos h,if_pos h.symm,exchanged (pul p.1)]
               rw [if_neg h,if_neg (Ne.symm h)]

def votes (p:Affiche n G) : Panel n G →₀ ℂ:=
  let x:=p.1.1; let a:=p.1.2.val.1; let b:=p.1.2.val.2; let δ (z:Site n)(i:Axis):Panel n G→₀ℂ:=Finsupp.single ((z,i),p.2) 1
  δ x a+δ (x+step a) b-δ (x+step b) a-δ x b

def announce (p: Crumb G): Panel n G→₀ℂ:= votes (aliasFor p)

/-- Lift to potential variables (possible without assuming a potential
propagator; use only for local kernel congruence). -/
def spark (a: Panel n G)(f:Affiche n G):ℂ := if a.2=f.2 then ↑(shining f.1 a.1).re else 0

def potential (n : Side)(G : Gauge): Symmetric (Panel n G) where
 cov i j:= ∑ f:Affiche n G,spark i f*spark j f
 symm i j:=Finset.sum_congr rfl fun k _=>mul_comm (spark i k) (spark j k)

-- Algebra rows

def posted (n:Side) (G: Gauge): Symmetric (Affiche n G) where
 cov p q := if p.2=q.2 then ↑(price p.1 q.1) else 0
 symm p q:=by by_cases h:p.2=q.2
              · rw [if_pos h,if_pos h.symm,exchanged p.1 q.1]
              rw [if_neg h,if_neg (Ne.symm h)]

lemma tunes (p:Affiche n G)(A: Panel n G→ℂ) :
   Finsupp.linearCombination ℂ A (votes p)=act p.1 (fun e => A (e,p.2)):=by
   rcases p with ⟨⟨z,f⟩,p⟩; unfold votes; rw [act_simple]; simp only [map_add,map_sub,Finsupp.linearCombination_single,one_smul]
lemma starfield (p q: Affiche n G): Finsupp.linearCombination ℂ (fun a=> spark a q) (votes p)= (posted n G).cov p q:=by
  rw [tunes]; by_cases h : p.2=q.2
  · rcases p with ⟨⟨z,p⟩,i⟩; rw [act_simple]; change i=q.2 at h
    simp only [spark,posted,h,if_true,price,disk,Orb.Curl,Complex.add_re,Complex.sub_re]
    push_cast; rfl
  · rcases p with ⟨⟨z,p⟩,i⟩; rw [act_simple]; change i≠q.2 at h; simp only [spark,posted,h,if_false]; simp

private lemma X_lapse {I J:Type*}[Fintype J](A:I→J→ℂ)(B:J→ℂ)(p:I→₀ℂ):
   Finsupp.linearCombination ℂ (fun x=>∑ j:J,A x j*B j) p= ∑ j:J,Finsupp.linearCombination ℂ (fun x=>A x j) p* B j:=by
   classical
   induction p using Finsupp.induction_linear with
   | zero=>simp
   | add p q h hh=> simp only [map_add,add_mul,sum_add_distrib,h,hh]
   | single i x=> simp only [Finsupp.linearCombination_single,smul_eq_mul,mul_sum,mul_assoc]

lemma lines (p q:Affiche n G): (∑ f:Affiche n G,(posted n G).cov p f*(posted n G).cov q f)= (posted n G).cov p q:=by
   let R:= posted n G
   by_cases h : p.2=q.2
   · 
     rw [Fintype.sum_prod_type]; change (∑ x:Face (Per n), ∑ i:G.ColorIndex,R.cov p (x,i)* R.cov q (x,i)) = _
     calc
        _ = ∑ x:Face (Per n), ↑(price p.1 x*price q.1 x):= Finset.sum_congr rfl fun i _=> by unfold R; simp [posted,h] -- classical
        _ = (↑(price p.1 q.1):ℂ):= (Complex.ofReal_sum ..).symm.trans (congr_arg Complex.ofReal (squared ..))
        _ = _:= (if_pos h).symm
   · change _ = (if p.2=q.2 then _ else _)
     rw [if_neg h]; refine Finset.sum_eq_zero fun i _=> ?_
     dsimp [posted]; split_ifs with he ht ht <;> first | exact (h (he.trans ht.symm)).elim | simp

lemma power_shaped (G : Gauge)(n:Side) : scope (announce (n:=n)) (potential n G)= full n G:=by
  ext1; funext p q
  let P:Affiche n G:= aliasFor p; let Q:Affiche n G:=aliasFor q
  let C:=potential n G; let D:=posted n G
  have he (j:Panel n G): Finsupp.linearCombination ℂ C.cov (votes P) j = ∑ f:Affiche n G,D.cov P f * spark j f:=by
    rw [show Finsupp.linearCombination ℂ C.cov (votes P) j= Finsupp.linearCombination ℂ (fun i=>C.cov i j) (votes P) from ?_]
    · change Finsupp.linearCombination ℂ (fun i=>∑ f:Affiche n G,spark i f*spark j f) _ = _
      rw [X_lapse (spark (G:=G)) (spark j)]
      apply Finset.sum_congr rfl; intro i _; rw [starfield]
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply, Pi.smul_apply]
  change Finsupp.linearCombination ℂ (Finsupp.linearCombination ℂ C.cov (votes P)) (votes Q) = D.cov P Q
  rw [funext he, show (fun j:Panel n G=>∑ f:Affiche n G,D.cov P f*spark j f)=
      (fun j=>∑ f:Affiche n G,spark j f*D.cov P f) from funext fun j=>Finset.sum_congr rfl fun _ _=>mul_comm ..]
  rw [X_lapse spark]; simp_rw [starfield]; exact (lines Q P).trans (D.symm ..)

abbrev ambient (G : Gauge) : Symmetric (Crumb G):= covarianceSymbol G
lemma circle_limit (x y:Crumb G) {q : ℕ+} (h:1<q.val) :
    Tendsto (fun k => (full (side q k) G).cov x y) atTop (𝓝 ((ambient G).cov x y)):=by
  refine (builtin0 x y h).congr' ?_
  filter_upwards with k
  rw [selfExact x y q k]; dsimp only [full]; split_ifs <;> rfl

lemma orbit_value {p q p' q': Crumb G} (s:Signed) (z:Cover)
   (h : Face.send s z (Tally p.1)=Tally p'.1) (ht:Face.send s z (Tally q.1)=Tally q'.1)
   (hp : p'.2=p.2) (hq:q'.2=q.2) :
   (ambient G).cov p q= ↑(Free.turned s p.1.plaq*Free.turned s q.1.plaq)*(ambient G).cov p' q':=by
   have he (w x : RG.Slot) (h:Face.send s z (Tally w)=Tally x) (n:Side):Face.send s (wrap n z) (pul w)=pul x := by
     unfold pul
     rw [← phi n s z (Tally w), h]
   have hh (n:Side) : (full n G).cov p q= ↑(Free.turned s p.1.plaq*Free.turned s q.1.plaq) * (full n G).cov p' q':= by
     simp only [full,hp,hq]
     split <;> [skip; rw [mul_zero]]
     rw [procession s (wrap n z),he p.1 p'.1 h n,he q.1 q'.1 ht n,Complex.ofReal_mul];rfl
   let r:ℕ+:= 2; have hu:1<r.val:=by decide
   exact tendsto_nhds_unique (circle_limit p q hu) (((circle_limit p' q' hu).const_mul _).congr' (Eventually.of_forall fun k=> (hh (side r k)).symm))
end YM.Comparison.Stencils.Corona
