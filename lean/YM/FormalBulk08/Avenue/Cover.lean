import YM.FormalBulk08.Avenue.Edit
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
variable {S T:Anthem D G}
lemma mat_greens (v:Train j)(hk:0<k)(hj:4≤j)(h:Wade o T l)(p:Studio D)(r:ℕ): Light (winner v k l T p r) (fun n=> marble r (binned v k n (Kemp.banner l (T p) n))):= by
    obtain ⟨η,hs,H⟩:=sunny _ _ h; exact (herder v hk hj h p hs (fun i=>by obtain ⟨C,hc,H⟩:= H i; exact ⟨_,H p⟩) r).1
lemma winner_pay (v:Train j)(hk:0<k)(hj:4≤j)(h:Glyph o T l 0)(r:ℕ) (p:Studio D):∃ η C:ℝ, 0<η ∧ Knoxville (fame _) η (0,o) (winner v k l T p r) C:= by obtain ⟨_,η,t,⟨A,_,H⟩,_⟩:= occupants v hk hj h r; exact ⟨η,_,t,H p⟩
lemma greens_plus (v:Train j)(hk:0<k)(hj:4≤j)(h:Wade o T l)(he:Wade o S l)(p:Studio D)(r:ℕ): winner v k l (T+S) p r=winner v k l T p r+winner v k l S p r:= by
    let V n:= Kemp.banner l ((T+S) p) n
    have ht n:binned v k n (V n) = binned v k n (Kemp.banner l (T p) n)+ binned v k n (Kemp.banner l (S p) n):= by unfold V binned; rw [Pi.add_apply, banner_add l (T p) (S p) n (h.summable _) (he.summable _),map_add,map_add]
    funext x; refine tendsto_nhds_unique (mat_greens v hk hj (h.add he) p r x) (((mat_greens v hk hj h p r x).add (mat_greens v hk hj he p r x)).congr ?_); intro n; change _ = marble r (binned v k n (V n)) _; rw [ht n,marble_add];rfl
lemma greens_launch (v:Train j)(hk:0<k)(hj:4≤j)(h: Wade o T l)(b:Pence)(p:Studio D)(r:ℕ): winner v k l (launch b T) p r= coeff 0 b • winner v k l T p r:= by
    have he n: binned v k n (Kemp.banner l ((launch b T) p) n)= coeff 0 b • binned v k n (Kemp.banner l (T p) n):= by
        unfold binned; rw [banner_mul h _ b n, show ∀ c d:Pap (wire G n),coeff 0 (c*d)=coeff 0 c * coeff 0 d from fun c d => by rw [coeff_zero_eq_constantCoeff_apply,map_mul,←coeff_zero_eq_constantCoeff_apply, ←coeff_zero_eq_constantCoeff_apply], show coeff 0 (worm (wire G n) b)= MvPolynomial.C (coeff 0 b) from coeff_map .., ← MvPolynomial.smul_eq_C_mul,map_smul]
    funext x; refine tendsto_nhds_unique (mat_greens v hk hj (h.launch b) p r x) (((mat_greens v hk hj h p r x).const_mul (coeff 0 b)).congr' (.of_forall (fun i=> ?_))); change _=marble r (binned v k i _) _; rw [he i, ← canyon_eq,map_smul];rfl
lemma clover_plus (F:Frame G d)(v:Train j)(hk:0<k)(hj:4≤j)(h:Glyph o T l 0)(he: Glyph o S l 0) (i :Letter F): clover F v k (T+S) l i= clover F v k T l i+clover F v k S l i:= by
    obtain ⟨η,C,h₁,hC⟩:=winner_pay v hk hj h (Pose.slots F i) (Pose.inside F i D); obtain ⟨ξ,B,h₂,hB⟩:= winner_pay v hk hj he (Pose.slots F i) (Pose.inside F i D); unfold clover; rw [greens_plus v hk hj h.summary he.summary]; exact chalk F _ _ hC hB h₁ h₂ _
lemma clover_launch (F:Frame G d)(v:Train j)(hk:0<k)(hj:4≤j)(h:Glyph o T l 0)(b:Pence)(i:Letter F): clover F v k (launch b T) l i= coeff 0 b*clover F v k T l i:= by
    obtain ⟨η,C,H,hC⟩:= winner_pay v hk hj h (Pose.slots F i) (Pose.inside F i D); unfold clover; rw [greens_launch v hk hj h.summary]; exact chalk_amp F _ hC H _
lemma clover_nil (o:Loc G 1)(F:Frame G d)(v:Train j)(hk:0<k)(hj:4≤j)(l:ℕ): clover F v k (0:Anthem D G) l=0:= by
    funext i; have ht:=clover_launch F v hk hj (from_clef (Clef.base (a:=o) (l:=l) (D:=D)) 0) 0 i; rw [map_zero,zero_mul,void_launch] at ht; exact ht
lemma clover_sums {I:Type*} (U:Finset I)(T:I→Anthem D G)(o:Loc G 1)(F:Frame G d)(v:Train j)(hk:0<k)(hj:4≤j)(h:∀ i∈U,Clef o (T i) l) (x:Letter F): clover F v k (∑ i∈U,T i) l x= ∑ i∈U,clover F v k (T i) l x:= by
    induction U using Finset.induction with
    | empty=>rw [Finset.sum_empty,Finset.sum_empty,clover_nil o F v hk hj];rfl
    | @insert i V he ih=> have hp j (hj:j∈V):=h j (Finset.mem_insert_of_mem hj); rw [Finset.sum_insert he,Finset.sum_insert he,clover_plus F v hk hj (from_clef (h _ (Finset.mem_insert_self ..)) 0) (from_clef (Clef.sum _ T hp) 0), ih hp]
lemma clover_align {I J:Type*}[Fintype I](F:Frame G d)(v:Train j)(hk:0<k)(hj:4≤j)(Y:I→ Anthem D G)(S:Matrix I J Pence)(h:∀ i,Clef o (Y i) l)(i j) : clover F v k (larch Y S j) l i=∑ x:I, clover F v k (Y x) l i *coeff 0 (S x j):= by
    unfold larch; rw [clover_sums Finset.univ _ o F v hk hj (fun x _=> (h x).launch (S x j))]; exact Finset.sum_congr rfl fun w hw=> by rw [clover_launch F v hk hj (from_clef (h w) 0)]; ring
-- W uses max d. column l distinct
variable {F:Frame G d}{Y:Plaza F D}
def Woven (F:Frame G d)(v:Train j)(k:ℝ)(Y:Roof.Plaza F D) : Matrix (Letter F) (Letter F) ℝ := fun i z=> clover F v k (Y z) d i
lemma woven_diagonal (v:Train j)(_hk:0<k)(_hj:4≤j)(h:Court o F Y)(x y:Letter F)(he:slots F y≤ slots F x): Woven F v k Y x y = if x=y then 1 else 0:= by
    let S:= Y y; have hp:= h.officers y; by_cases ht:slots F x=slots F y
    · unfold Woven clover; have hz:= echo_nil F S x; have hx : winner v k d S (Pose.inside F x D) (slots F x) = S (Pose.inside F x D) 0 (Pose.slots F x):= by rw [ht]; exact crown_king v k _ hp.fare _
      change pearlJ F (winner v k d S (Pose.inside F x D) _) _=_; rw [hx,← hz]; unfold S; rw [Court.city h]; by_cases h:x=y <;> simp [h]
    rw [if_neg (fun h'=>ht (congr_arg (Pose.slots F) h')),Woven]; unfold clover; rw [show winner v k d (Y y) (Pose.inside F x D) (Pose.slots F x)=0 from crown_zero v k _ hp.fare _ (lt_of_le_of_ne he (Ne.symm ht)), chalk_void]
lemma wallpaper (F:Frame G d)(H:Hol G)(hp:d<D)(o:Loc G 1)(ρ:ChartRatio G)(a:hue G)(P:Flight j u)(V:Lodge P.patch){K:KernelChoices}(h:P.patch.Branches K G)(W:Pot G)(hv:Story W (pink K.penalty P.wing))(hr:LocalRatio ρ)(ht:4≤u)(hd:d≤j)(hL:2≤P.L.val)(Y:Roof.Plaza F D)(hY:Court o F Y):
   let U:=pTrain F ρ a P V h hL W Y; let Q:=avenue F ρ a P V h hL W Y
   Woven F P.land K.penalty Q*preTable U=noncontract F U * Woven F P.wing K.penalty Y:= by
   intro U Q; ext i x
   let L:=migrates a P V K W ρ h hL d d ∘ Y
   obtain ⟨he',he⟩:=axle F ρ a P V h hL W Y hY hv hr H hp hd ht; change larch Q U=L at he
   rw [Matrix.mul_apply,Matrix.mul_apply]; change (∑ z,clover F P.land K.penalty (Q z) d i*coeff 0 (U z x))=_; rw [← clover_align F P.land K.penalty_pos ht Q U (fun i=> clef_through (he'.officers i) (slotsFits F i)), he]; exact congr_fun (migration F H hp Y hY P V h W hv ρ hr ht hd hL a (Y x) (clef_through (hY.officers x) (slotsFits F x)) d le_rfl) i
end YM.FormalBulk08.Avenue
