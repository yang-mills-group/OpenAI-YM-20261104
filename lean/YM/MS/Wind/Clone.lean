import YM.MS.Wind.Dawn
/-!
# Transport the Taylor table to the actual solutions

Light weighted differences rank via unique PDE. No Gram relation needed. Remember
 all t. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p q:Team}{φ φ':Actor G}{F H V: Dec G}{b:Bool}{k r d:ℕ}{l:List (Lane4 G)}{u:ℤ}
-- eq solution across forcing
lemma term_near {Z W:Pack G} {F:ℝ→ Wind.Flow G} {A C:ℝ→ Law G} (hZ:Fees b u Z)(hW:Fees b u W) (H:∀ x, Sat (A x) (Z x) (F x))(he:∀ x,Sat (C x) (W x) (F x))(x:ℝ): Near false ((Z-W) x):= by
   obtain ⟨v,hv⟩:=hZ.pay; obtain ⟨t,h⟩:=hW.pay; exact Touch_near (hZ.stay x) (hW.stay x) (H x) (he x) (hv x) (h x)
lemma term_copy {Z W:Pack G} {F:ℝ→Wind.Flow G} {A:ℝ→ Law G} (hZ:Fees b u Z)(hW:Fees b u W) (H:∀ x, Sat (A x) (Z x) (F x))(he:∀ x,Sat (A x) (W x) (F x)) : Z=W:= by
    apply sub_eq_zero.mp; funext i; exact Dtotal (term_near hZ hW H he i) (by change Z i 0-W i 0=0; rw [(H i).1, (he i).1, sub_self])
lemma step_birth (hp:PC G p F)(hq:PC G q H)(h:∀ i,i<k→p i=q i) : ∀ i<k,F i=H i:= by
   intro i; induction i using Nat.strong_induction_on with
   | _ i ih=>
      intro he; by_cases hh: i=0; · subst i; rw [hp.free,hq.free]
      have hi : 0 < i:= Nat.pos_of_ne_zero hh; have ha: path (1/2) i 1 F F=path (1/2) i 1 H H:= path_eq _ _ _ (fun j hj=> ih (i-j) (by obtain h:=path_in hj; omega) (by obtain h:=path_in hj; omega)) (fun j hj=>ih j (path_in hj).2 (by obtain h:=path_in hj; omega));
      refine term_copy (hp.owes i) (hq.owes i) (hp.recu _ hi) (fun t=>?_); rw [ha, show style G p t i=style G q t i from Native.Wilsonian.remember t _ (fun j hv=> h j (by omega))]; exact hq.recu _ hi t
lemma mark_birth (hp:PM φ V F u)(hh:PM φ' V H u) (h:∀ i, i<k→ ∀ x, φ x i=φ' x i): ∀ i<k,F i=H i:= by
   intro i; induction i using Nat.strong_induction_on with
   | _ i ih=>
       intro he; refine term_copy (hp.owes i) (hh.owes i) (hp.recu i) (fun t=>?_); rw [h i he, path_eq 1 i 0 (fun _ _=>rfl) (W:=H) (fun j hj=> ih j (path_in hj).2 (by obtain h:=path_in hj; omega))]; exact hh.recu ..
-- angle only meaningful in t^≥0 comparisons
structure Knick (P Q:Pack G)(r:ℕ)(h:ℤ)(b:Bool)(W:ℝ→ Law G): Prop where
    size x: Rank ((P-Q) x) r
    pay x t w (he:Course b w) (hp:w.length=r) (j:ℕ) (hv:fieldDim wfield w+j ≤h): torch j (((P-Q) x) t) w=if fieldDim wfield w+j=h then W x w else 0
lemma knick {P Q Z:Pack G} {A C:ℝ→ Dot G Cover} (hP:Fees b u P)(hQ:Fees b u Q)(hf: ∀ x, Sat (run (A x)) (P x) (Z x)) (hh:∀ x,Sat (run (C x)) (Q x) (Z x)) {J:ℝ→ Law G}{v:ℤ}(h:∀ x, Fits (A x-C x) (J x) r v b) (hv:∀ x, Limit (A x-C x).val r): Knick P Q r v b J:= by
    have he x: (P x-Q x) 0=run (A x-C x):= by rw [Pi.sub_apply,(hf x).1,(hh x).1,map_sub];
    have hr x := Dprecise (F:=P x-Q x) (term_near hP hQ hf hh x) (show Limit ((P x-Q x) 0) r from he x ▸ Tone.oneRank (hv x))
    refine ⟨fun x=> (hr x).1,fun x t w hw hh j h'=>?_⟩;
    rw [← face_here (h x) hw j h']; unfold torch; rw [show fieldVal ((P-Q) x t) (ray w)=_ from funext ?_]; intro a; unfold fieldVal;
    have ht : ((sail (ray w) a).length:ℤ)=r:= (by simp [hh]); rw [enough _ ht, show (P-Q) x t _=(P x-Q x) 0 _ from (hr x).2 _ ht t, he x]

lemma bulk_pay {L:ℝ→ Law G} (hf:PC G p F)(hh:PC G q H)(h:Career G p q k r u L)(hp:1≤k): Knick (F k) (H k) r u true L:= by
   have he := step_birth hf hh h.past; have hL:path (1/2) k 1 F F=path (1/2) k 1 H H:= by apply path_eq; intro i hi; apply he; obtain h:=path_in hi; omega; intro i hi; exact he _ (path_in hi).2
   exact knick (hf.owes k) (hh.owes k) (hf.recu _ hp) (fun x=> by rw [hL]; exact hh.recu _ hp x) h.jet h.size
-- Pipes selection independent of pack-reading scale

def skyline (G:Gauge)(p:Team): Dec G:= (space_H G p).choose
lemma skyPC (G:Gauge)(p:Team): PC G p (skyline G p):= (space_H G p).choose_spec
variable {B: Local.Physical.Deck G} (W:LitBook B)
-- mark with canonical action; uses all t, 'A arbitrary finite dimensions.'
def horizon (W:LitBook B)(p:Team)(A:Acts B d): Dec G:= (member (skyPC G p) (decor W p A)).choose
lemma aqua (W: LitBook B)(p:Team)(A:Acts B d): PM (score W p A) (skyline G p) (horizon W p A) 0 := (member (skyPC G p) (decor W p A)).choose_spec
lemma money_before (A C:Acts B d)(h:∀ i<k,A i=C i) : ∀ i<k,horizon W p A i=horizon W p C i:= mark_birth (aqua W p A) (aqua W p C) (fun j hj x=> steady W p A j C (fun i hi=>h i (by omega)) x) -- order of steady args?
lemma mark_pay {Z:ℝ→ Law G}{A C:Acts B d}(hf:Capacity W p A C k r u Z): Knick (horizon W p A k) (horizon W p C k) r u false Z:= by
    let T:= horizon (d:=d) W p; let F':=skyline G p; have he: path 1 k 0 F' (T A)=path 1 k 0 F' (T C):= path_eq _ _ _ (fun _ _=>rfl) (fun i hv=> money_before W A C hf.past _ (path_in hv).2)
    refine knick ((aqua W p A).owes k) ((aqua W p C).owes k) ((aqua W p A).recu k) (fun x=>?_) hf.jet hf.size; rw [he]; exact (aqua W p C).recu k x
end YM.MS.Wind
