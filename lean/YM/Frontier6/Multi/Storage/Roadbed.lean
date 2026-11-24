import YM.Frontier6.Multi.Storage.Station
import YM.MergeProof.North.Dolphin

/-! Walking coarsewards, shrinking only at decreasing-arity stops. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V C O:Type}[Fintype V][DecidableEq V][Fintype O][DecidableEq O][Fintype C][DecidableEq C]
variable {G:Gauge}
section
variable (H:History G)(δ:ℕ→ℝ)(r:ℕ→ℕ)(D:∀ N p i,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
variable {N p i:ℕ}(σ χ:ℕ→ℝ)(v:V) (P:V→Motion)(B:V→Equiv.Perm V)
   (E:∀ i:ℕ,V→Site (H.S.side i p))(o:∀ i:ℕ,Live V O→Site (H.S.side i p))
set_option quotPrecheck false
local notation "P'"=> H.levels.budget
local notation "R"=> H.rep N p
local notation "X"=> (Now V O)
variable (h:H.Selected)(μ:ℕ)(hr:Thor H δ r D σ χ μ) (w0:ℝ)
local notation "c!"=>fun i:ℕ=>Salt.scent (P' i).B (r i) ((P' i).supportExponent+1/2) 1 (δ i) 1 (χ i)
local notation "n"=> Fintype.card O
variable (F:Config G (H.S.side N p)→Poly (Now V O))
local notation "Y"=> gust H N p N F
variable (root:O){π:Concentrate O C} (ε:ℝ) {m j:ℕ}
local notation "M!"=> Next.Foundations.localSection G d
include h hr
lemma supplied (d:ℕ)(hm:m<N)(hx:μ ≤ m)(hF: Integrable F (prior G _))
    (hp:Port H v P E o w0 F root hm)(he:(fun y=>o (m+1) (y,root))=E (m+1))(hU:E m v=0)(hE:(H.levels.clock.op m p).ratio.embed ∘ E m=E (m+1))(hP:P v=(1,false))(hO:Occupancy (E (m+1)) (r m))(hd:Occupancy (E m) (r m))
    (x:ℝ)(W:V→ℝ)(hX:Throws H N p m (D N p m hm) (Next.Foundations.hol G) (Next.Foundations.localSection G d) x)(hw:0<w0)(hx':1 ≤ x)(hv:∀ i,0<W i)(hg:∀ i,W i ≤ δ m*(w0/(16*x))):
    let z:=H.S.a (m+1)^d*(x*(1/(2*w0))); let U:=Next.Foundations.localSection G d
    ∃ Q₀:Coefficient ((Labels.frames G).level d) (H.S.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m)∧Q₀.remBound 0 (R m) (kappa H m) z∧ ((Labels.frames G).level d).coeffSize Q₀.x ≤ z ∧ Served (R m) (fun i=> radiant (alto H m d) (P i) (E m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=>sunny (R m) Q₀.forced (P i) (E m i) (alto H m d)) ((droplet root).reap ∘ gust H N p N F m hm.le) (E m) W ((P' m).supportExponent) 1:=by
    intro z U; let Q:= H.rep N p (m+1); let T:= H.levels.clock.op m p; have he' : (fun j=>T.ratio.embed (E m j))=E (m+1):= hE
    let w(i:V):= w0/(16*x); have hx0:0 < x:=zero_lt_one.trans_le hx'; have hw'(i):0 < w i:= div_pos hw (by positivity)
    have hh (i):w i ≤ 1*w0:=by rw [one_mul]; exact div_le_self hw.le (by linarith only [hx'])
    have hν:T.ratio.parent ∘ E (m+1)=E m:=by rw [← he']; exact funext (fun _=> T.ratio.embed_parent ..)
    let Ω:=droplet (V:=V) root; obtain ⟨g,k,hY,hA,hr',hV⟩:= hp.pays; rw [he] at hY
    let Y':=gust H N p N (Ω.reap ∘ F); have hφ (i)(hi:i≤N): Ω.reap ∘ Y i hi=Y' i hi:= (Ω.gust_from _ hF hi).symm
    have hs : E (m+1) v=0 :=by rw [← he']; dsimp only; rw [hU]; exact T.ratio.root.map_zero
    rw [hφ] at hY ⊢
    let k'(i):=profile Q.activities (k i); have hu:(fun i=> stepUp (P v) (E (m+1) v) (g i))=g:=by rw [hs,hP]; exact funext fun _=> Ribbons.stepid ..
    have hi(j):g j= stepUp (P j) (T.ratio.embed (E m j)) (g v) ∧ k' j=floatUp (P j) (T.ratio.embed (E m j)) (k' v):=by
       rw [show T.ratio.embed (E m j)=_ from congr_fun he' j]; by_cases hp:j=v
       · subst j; rw [hs,hP,Ribbons.stepid,Ribbons.floatid]; exact ⟨rfl,rfl⟩
       exact hV j hp
    have hb:Blade Q 0 (g v) (k' v) 0 (1/(2*w0)):= by
       rw [show 0=o (m+1) (v,root) from (Eq.trans (congr_fun he v) hs).symm]; exact hr' -- rw second zero?
    have hxk: Integrable (Ω.reap ∘ F) (prior G _):= (Ω.reap.restrictScalars ℝ).integrable_comp hF
    have hε : Repegs (E m) (P' m).B (fun i=> δ m*w i) W (1/2) 1 (Bud V):=by
       intro i he j hj; rw [one_mul]; exact (prod_le_prod (fun i _=>hv i|>.le) (fun i _=>hg i)).trans (le_mul_of_one_le_right (prod_nonneg (fun i _=>mul_nonneg (hr.suns m hx).hats.1.le (hw' i|>.le))) (Real.one_le_exp (by positivity)))
    show ∃ Q₀:_, _
    have hc : ∀ i, 2*w i * (2*(1/(2*w0))) ≤ 1:=by intro i; unfold w; field_simp; nlinarith only [hx',hx0,hw, mul_le_mul_of_nonneg_right hx' hw.le]
    have hz' : ∀ i,w i* (‖(((H.S.block m).val:ℂ)^d)⁻¹‖*(x*(1/(2*w0))))≤1:=by
      intro i; let L:=((H.S.block m).val:ℂ)^d; have hU:1 ≤ ‖L‖:= by unfold L; rw [norm_pow,Complex.norm_natCast];exact one_le_pow₀ (by exact_mod_cast (H.S.block m).property)
      have hx: ‖L⁻¹‖ ≤ 1:= by rw [norm_inv]; exact inv_le_one_of_one_le₀ hU
      refine (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (show 0≤ x*(1/(2*w0)) from by positivity) hx) (hw' i).le).trans ?_; unfold w; field_simp; linarith
    obtain ⟨Q₀,hY,hσ,hB,hZ⟩:= Ribbons.fuseNext H d r (θ:= Y' (m+1) hm) h hm (hr.suns m hx) (hr.moon N p m hx hm).1 hw' hv (hY.prune (u:=(H.levels.budget (m+1)).supportExponent) (fun _=>hw) hw' (slighter (fun _=>hw) hw' hh zero_le_one le_rfl) zero_le_one (by simp) (by norm_num : (1:ℝ)*1 ≤ 1)) (by linarith only) hO (by rw [show (H.levels.clock.op m p).ratio.parent ∘ E (m+1)=_ from hν]; exact hd) hA hb he'.symm hi hX hx0.le hc hz' hε (gust_live _ _ _ _ _ hxk hm)
    change Served _ _ _ _ _ _ _ _ at hZ
    have hu: Y' m hm.le=T.push Q.beta (Y' (m+1) hm):=gust_step ..
    rw [hu]; exact Ribbons.crescent H d hY hσ hB hZ


lemma inaugural (w:O→ℝ)(hj:j<N)(he:μ < j)(hS:Atlas H v P B E o δ χ j (N:=N) (Y j hj.le) (fun i=>8*w i)) (hχ:χ j ≤ 1)(hw:∀ i,0<w i) : Storage H v P B E o root F j j hj.le ε (total w):=by
    have hA:Arsenal (R j):=by cases j; omega; exact (hr.moon _ _ _ (by omega) (by omega)).1.contact
    have hh:= activation v P B E o h μ hr (fun i=>8*w i) _ hS (fun i : O=> mul_pos (by norm_num) (hw i)) hA hj.le hχ he.le
    let π:=Concentrate.identity O
    have hp:(batt (V:=V) π).reap ∘ Y j hj.le=Y j hj.le:=funext (fun x=> Concentrate.reap_id _)
    refine ⟨O,inferInstance,inferInstance,π,root,w,rfl,by rw [Nat.sub_self,warrant_start],?_⟩
    rw [hp]; rw [show (fun j:O=> (8*w j)/8)=w from (by ext; ring)] at hh; exact hh
end
end YM.MergeProof.Canopies
