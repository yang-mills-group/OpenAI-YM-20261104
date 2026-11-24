import YM.RG16.Unmasked.Purchased

/-!
# Keep the page -- compare on this pinned vacuum

An origin page needs `Ink`, not continuity or boundedness of the raw
projection, to keep its denotation through OPE estimates. This is the full
marked-density, no positivity assumed of those complex λ coefficients. Not a
norm on densities per se. Definitions lifted from Stencil of `Family`. On the
higher-order portion in this file-set these have to be *same*, with all flags
and supports. At calls to `Gate` the resident representatives already pay
**full** masking/support costs; equality of their denotations suffices in
transmitting ANY true values at occ, regardless of intermediate label choices,
because of the lineage being ONE persistent mark. Not usable for replacing
singletons after a multi-marker step (see RG16 qass plans).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Guarding
open Set Function Filter Lattice Labels Wilson Source RG OPE MeasureTheory
open Extra.Histories Relay Bid Cells MergeProof Next.Foundations
open Pert Trace.Physical Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato.Bandage Work.G08
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}(C:Family G)(N p d:ℕ)
set_option quotPrecheck false
local notation "Λ" => Lambda C.path.levels
local notation "F" => C.labels.level d
local notation "W" => C.label d
local notation "Rep!" => C.path.rep N p
local notation "D" => measuring C d N p
local notation "s" => (C.labels.level d).coeffSize
local notation "Θ" => value (C:=C) d N p
local notation "λ₀" => factor C
local notation "V" => calValues (C:=C) d N p

abbrev Ink (i:ℕ) (f : Config G (C.side i p)→ℂ)(u : C.label d)(x:ℝ) :=
    ∃ q : store C d p i, reads d N p i q x ∧ page d p i q=u ∧ f= value (C:=C) d N p i q

def accepted (i:ℕ)(f : Config G (C.side i p)→ℂ)(u:C.label d) := ∃ x:ℝ,Ink C N p d i f u x
abbrev Nullity (i:ℕ)(f : Config G (C.side i p)→ℂ) (x:ℝ) := Ink C N p d i f 0 x

section
variable {C N p d}
variable {i:ℕ}{f g : Config G (C.side i p)→ℂ}{u v: C.label d}{x y : ℝ}

lemma ink_eq (hC:C.Makes)(hp:C.ref d ≤ i)(hN:i ≤ N)(hu: Ink C N p d i f u x)
    (hv: Ink C N p d i f v y) : u=v := by
   obtain ⟨b,hb,H,rfl⟩:= hu; obtain ⟨c,hc,Q,G⟩:= hv
   exact H.symm.trans ((same_page hC hN hp hb hc (EventuallyEq.of_eq G)).trans Q)

lemma Ink.pred (h:Ink C N p d i f u x): accepted C N p d i f u:= Exists.intro _ h
lemma Ink.ok (e:Ink C N p d i f u x): 0≤x:=by obtain ⟨q,h,-⟩:= e; exact rem_nonneg h.2
lemma Ink.message (h:C.Makes)(hT:C.ref d ≤ i)(hN:i≤N)(hx:Ink C N p d i f u x): Integrable f (prior G (C.side i p)):= by
    obtain ⟨q,hq,h₀,rfl⟩:=hx; exact GermGraph.message d N p i h hT hN hq
lemma Ink.inc (h : Ink C N p d i f u x)(e:x≤y): Ink C N p d i f u y:= by obtain ⟨q,a,e'⟩:=h; exact ⟨q,⟨a.1,rem_increase d a.2 e⟩,e'⟩
lemma Ink.combine (hf:Ink C N p d i f u x)(hg:Ink C N p d i g v y)(h:C.Makes)(hT:C.ref d ≤ i)(hN:i ≤ N): Ink C N p d i (f+g) (u+v) (x+y):= by
   obtain ⟨q,hq,H,rfl⟩:=hf; obtain ⟨b,hb,Q,rfl⟩:= hg
   refine ⟨beside q b, presentation hq.1 hq.2 hb.1 hb.2, (addPage d N p i q b h hT hN hq hb).trans ?_,
     (plus (h.wilson.represents N p i hN |>.good) hq.2 hb.2 (C.localSection d)).symm⟩
   rw [H,Q]

private lemma stretch_project {h:store C d p i} (he:reads d N p i h x) (k:ℂ)(H:C.Makes)(hT:C.ref d ≤ i)(hN:i≤N) : page d p i (stretch k h) = k • page d p i h := by
    let m(a:ℂ):= stretch a h; let κ:= (Rep! i).p.threshold
    have hz: m 1 = h := by simp only [m,Extra.Histories.stretch, one_smul]
    have hQ(a:ℂ): reads d N p i (m a) (‖a‖*x):= ⟨stretch_format a he.1, stretch_rem a he.2⟩
    have hl : IsLinearMap ℂ (fun a:ℂ=>(m a).x) ∧ IsLinearMap ℂ (fun a:ℂ=> (m a).regular):=
       ⟨⟨fun a b=>add_smul ..,fun a b=>smul_assoc ..⟩,⟨fun a b=>add_smul ..,fun a b=>smul_assoc ..⟩⟩
    have hp:= dimensions d N p i H hT hN
    have hv:= Germ.linear_projection (F) C.params (o:=0) m hp.1 hp.2 (fun a=>(hQ a).1) (fun a=>⟨_,_,(hQ a).2⟩) hl
    have hs := (H.wilson.represents N p i hN).vac
    unfold page plank; rw [←hs];
    simpa only [smul_eq_mul,mul_one,hz] using hv.map_smul k 1

lemma Ink.scale (e:Ink C N p d i f u x)(k:ℂ)(H:C.Makes)(hT:C.ref d ≤ i)(hN:i≤N) :
    Ink C N p d i (k • f) (k • u) (‖k‖*x):= by
   obtain ⟨q,hq,hv,rfl⟩:=e
   exact ⟨stretch k q,⟨stretch_format k hq.1,stretch_rem k hq.2⟩, (stretch_project hq k H hT hN).trans (congr_arg _ hv), funext fun t=> (stretch_density ..).symm⟩
lemma Nullity.neg (e:Nullity C N p d i f x)(H:C.Makes)(hT:C.ref d ≤ i)(hN:i≤N) : Nullity C N p d i (-f) x:= by simpa only [neg_smul,one_smul,neg_zero,norm_neg,norm_one,one_mul] using Ink.scale e (-1) H hT hN
lemma Nullity.combine (e:Nullity C N p d i f x)(q:Nullity C N p d i g y)(H:C.Makes)(hT:C.ref d ≤ i)(hN:i≤N) : Nullity C N p d i (f+g) (x+y):= by simpa only [add_zero] using Ink.combine e q H hT hN

lemma foreground_fee {a b:ℝ}{bP:store C d p i}(e : reads d N p i bP a)(hu:s bP.x ≤ a) 
    (h:(1+4*stock C i)*a ≤ b) : Foreground C d N p i (Θ i bP) b := ⟨a,bP,size_nonneg (F) _ |>.trans hu,e,hu,rfl,h⟩

lemma foreground_splits (e : Foreground C d N p i f x)(H:C.Makes)(ho:Opened C d i p)(hN:i≤N):
    ∃ u: C.label d, mCost C d N p i u ≤ x ∧ Nullity C N p d i (f - V i u) x:= by
   obtain ⟨a,q,h0,hq,hx,Hf,ht⟩:= e
   obtain ⟨b,v,hp,hb,hr,hg,hA⟩:= fresh_split H ho hN _ hq hx
   refine ⟨v, le_trans hA ?_, Ink.inc ?_ ht⟩
   · exact le_trans (mul_le_mul_of_nonneg_right (show 2≤1+4*stock C i from by
       have := (stage C i).columns_ge; change _ ≤ _+_*((stage C i).columns);linarith) h0) ht
   refine ⟨b,hp,hb,?_⟩
   rw [←Hf,hr,add_sub_cancel_right]

lemma Ink.invest (H:C.Makes)(ho:Opened C d i p)(hN:i ≤ N)(x:C.label d):
     Ink C N p d i (V i x) (measuring C d N p i x) (2*stock C i*s (D i x)):=
   ⟨(C.factory d N p).entries i x, graph_cost d N p i H ho hN _, rfl,rfl⟩
lemma accept_cal (H:C.Makes)(ho: Opened C d i p)(hN:i≤N)(x:C.label d) : accepted C N p d i (V i x) (D i x):=Ink.pred (Ink.invest H ho hN x)
lemma accepted.combine (hx:accepted C N p d i f u)(he:accepted C N p d i g v)(H:C.Makes)(ho: Opened C d i p)(hN:i ≤ N) : accepted C N p d i (f+g) (u+v) := by
    obtain ⟨x,hx⟩:=hx; obtain ⟨y,he⟩:=he; exact Ink.pred (Ink.combine hx he H ho.post hN)
lemma accepted.scale (hx:accepted C N p d i f u)(c:ℂ)(H:C.Makes)(ho: Opened C d i p)(hN:i ≤ N) : accepted C N p d i (c • f) (c • u) := by obtain ⟨x,hx⟩:=hx; exact Ink.pred (Ink.scale hx c H ho.post hN)
lemma accepted.min (hf:accepted C N p d i f u)(he:accepted C N p d i f v)(H:C.Makes)(ho:Opened C d i p)(hN:i ≤ N): u=v:= by obtain ⟨x,hx⟩:= hf; obtain ⟨y,hz⟩:= he; exact ink_eq H ho.post hN hx hz

lemma nullity_toss {γ r:ℝ} (φ: Config G (C.side (i+1) p)→ℂ) (hk:Gate C d N p i γ 1)
    (hφ: Nullity C N p d (i+1) φ r) :
   ∃ y:C.label d, mCost C d N p i y ≤ factor C i ^(-rate)*r ∧
     Nullity C N p d i (transition (C:=C) d N p i φ - V i y) (factor C i ^(-rate)*r):= by
    obtain ⟨q,hq,hQ,rfl⟩:= hφ
    obtain ⟨t,y,ht₁,hT,hx,he⟩:=hk.2 q r hq hQ
    refine ⟨y,?_,t,ht₁,hT,?_⟩
    · have hl := zero_lt_one.trans (factor_positive C i)
      have hv:0<factor C i^rate:= Real.rpow_pos_of_pos hl _
      rw [Real.rpow_neg hl.le,mul_comm,←div_eq_mul_inv]
      replace hx:= hx.trans_eq (one_mul _)
      exact (le_div_iff₀ hv).mpr (by rw [mul_comm]; exact hx)
    rw [he,add_sub_cancel_right]
end
end YM.RG16.Guarding
