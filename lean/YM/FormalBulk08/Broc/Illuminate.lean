import YM.FormalBulk08.Broc.Ends

/-! Shelf-facing statement. Usable at *each* chosen budgeted width in the
input mesh. Numerical costs still declared: pencil sizes chosen BEFORE L
(add as many needed postmarks to receipts independently). Summations literal
not graphwise path histories. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Aster Dove Dove.Lab Next.Free Precision
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{K:KernelChoices}{n:Side}{r t e E:ℕ}{A B σ η:ℝ}{W:Lab G K I}{ρ:ChartRatio G}
lemma inks_treaty (u: hue G)(h:Use W ρ E)(p:LocalRatio ρ)(hs:G.Simple)(x:Leaf W.scrolls): Temper (heir u ρ W x.a x.b) E ∧ Sane (heir u ρ W x.a x.b) E:= by
    let T:=heir u ρ W x.a x.b
    have he:=born u x h p hs
    have hb i (hi:i≤E): stopper T E i=T i:= if_pos hi
    change Temper T E ∧ Sane T E
    exact ⟨⟨fun i hi r=>hb i hi ▸ he.civil i r,fun i hi r=>hb i hi ▸ he.agate i r,fun i hi r=> hb i hi ▸ he.valence i r,fun n=>clamps u h p hs x n⟩,fun a i hi hp=> (limited_seal u h p hs x hi hp).water 1 1 a a 0 0⟩
-- direct numerical function regardless on all G
structure Pencils (G:Gauge)(E:ℕ)(σ A B:ℝ):Prop where
     width:0<A
     cost:0≤B
     ink (T:Pot G)(u): Fits T E σ u → Temper T E → Sane T E → ∃ P,PrintK T E 0 (E+1) A (u*B) P

def bladeC (G:Gauge)(E:ℕ)(σ:ℝ):= if h:G.Simple∧0<σ then (printable G h.1 E σ h.2).choose else 1
def shadePrice (G:Gauge)(E:ℕ)(σ:ℝ):ℝ:= if h:G.Simple∧0<σ then (printable G h.1 E σ h.2).choose_spec.choose else 0
lemma width_price (hs:G.Simple)(hp:0<σ):Pencils G E σ (bladeC G E σ) (shadePrice G E σ):= by rw [bladeC,shadePrice,dif_pos (And.intro hs hp),dif_pos (And.intro hs hp)]; let H:=(printable G hs E σ hp).choose_spec.choose_spec; exact ⟨H.1,H.2.1,H.2.2⟩
section costs
variable (hp:Use W ρ E)(h:LocalRatio ρ)(hs:G.Simple)(a:hue G)
include hp h hs
lemma holdings : ∃ B:Leaf W.scrolls→ℝ, Soft (chron _) B ∧ (∀ i,0≤B i) ∧ ∀ x:Leaf W.scrolls,Fits (heir a ρ W x.a x.b) E (W.windowD x) (B x) ∧ ∀ N,x.b≤N→ Fits (saga ρ a W x.a N x.b) E (W.windowD x) (B x) ∧ Fits (saga ρ a W x.a N x.b-heir a ρ W x.a x.b) E (W.windowD x) (B x*fare_n x N) := by
    let X:=Leaf W.scrolls; let τ:=chron W.scrolls; let J:=Fin (E+1) × Fin (E+3)
    choose B H b hb using fun i:J=> diadem a hp h hs (Nat.le_of_lt_succ i.1.isLt) i.2.val
    choose M P m hm using fun i:J=> tenuous a hp h hs (Nat.le_of_lt_succ i.1.isLt) i.2.val
    let C:Leaf W.scrolls→ℝ:= fun x=>∑ j:J,(B j x+M j x)
    have hx j x: 0≤B j x+M j x:=add_nonneg (b j x) (m j x)
    have hw i:0≤C i:= Finset.sum_nonneg fun j _=> hx j i
    have hy x (i:J): B i x+M i x≤C x:= Finset.single_le_sum (fun j _=> hx j x) (Finset.mem_univ i)
    have hd x (i:J): B i x≤C x:= le_trans (le_add_of_nonneg_right (m i x)) (hy x i)
    have hm' x (i:J): M i x≤C x:= le_trans (le_add_of_nonneg_left (b i x)) (hy x i)
    refine ⟨C,soft_bill _ (fun i _=>(H i).plus (P i)),hw,fun x=>?_⟩
    have ht:= (inks_treaty a hp h hs x).1
    have ho e (he:e≤E) j (hp:E+3≤j): heir a ρ W x.a x.b e j=0:= by by_contra u; have h:=ht.valence e he j u;omega
    refine ⟨⟨hw x,fun e he j=>?_⟩,fun N H=>?_⟩
    · by_cases h:j<E+3
      · let v:J:=(⟨e,Nat.lt_succ_of_le he⟩,⟨j,h⟩); exact ((hb v x).1).mono (hd x v)
      rw [ho e he j (by omega)]; exact (bail_void ..).mono (hw x)
    have hf:= genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) _ a h hs H
    have hr e (he:e≤E) j (hp:E+3≤j): saga ρ a W x.a N x.b e j=0:= by change Dove.model _ _ _ _ _ _ _ _ _=0; by_contra u; have he':=hf.valence _ _ u;omega
    have hQ:0≤fare_n x N:=(ratioR_pos ..).le
    refine ⟨⟨hw x,fun e he j=>?_⟩,mul_nonneg (hw x) hQ,fun e he j=>?_⟩
    · by_cases h:j<E+3
      · let v:J:=(⟨e,Nat.lt_succ_of_le he⟩,⟨j,h⟩); exact ((hm v x N N H le_rfl).1).mono (hm' x v)
      rw [hr e he j (by omega)];exact (bail_void ..).mono (hw x)
    by_cases h:j<E+3
    · let v:J:=(⟨e,Nat.lt_succ_of_le he⟩,⟨j,h⟩); exact ((hb v x).2 N H).mono (mul_le_mul_of_nonneg_right (hd x v) hQ)
    rw [Pi.sub_apply,Pi.sub_apply,hr e he j (by omega),ho e he j (by omega),sub_zero];exact (bail_void ..).mono (mul_nonneg (hw x) hQ)

def treasure (W:Lab G K I)(E:ℕ)(x:Leaf W.scrolls):= bladeC G E (W.windowD x)
omit hp h hs in
lemma coin_nonneg (G:Gauge)(E:ℕ)(σ:ℝ):0≤shadePrice G E σ:=by unfold shadePrice;split
                                                             next p=>exact (printable G p.1 E σ p.2).choose_spec.choose_spec.2.1
                                                             exact le_rfl
-- actual users demand Soft of shadePrice and also Soft reciprocal of blade from schedule. No local log budget exchange hidden.
def Render (W:Lab G K I)(E:ℕ):Prop:= Soft (chron _) (fun x=>shadePrice G E (W.windowD x)) ∧ Soft (chron _) (fun x=> (treasure W E x)⁻¹)
lemma reported (u:Render W E): ∃ B:Leaf W.scrolls→ℝ, Soft (chron _) B ∧ (∀ i,0≤B i) ∧ ∀ x:Leaf W.scrolls,(∃ P,PrintK (heir a ρ W x.a x.b) E 0 (E+1) (treasure W E x) (B x) P) ∧ ∀ N,x.b≤N→
      ∃ P Q,PrintK (saga ρ a W x.a N x.b) E 0 (E+1) (treasure W E x) (B x) P ∧ PrintK (saga ρ a W x.a N x.b-heir a ρ W x.a x.b) E 0 (E+1) (treasure W E x) (B x * fare_n x N) Q:= by
    obtain ⟨B,b,H,F⟩:= holdings hp h hs a; refine ⟨_,b.times u.1,fun i=> mul_nonneg (H i) (coin_nonneg ..),fun x=>?_⟩
    obtain ⟨_,_,R⟩:=width_price (E:=E) hs (hp.zero x); obtain ⟨hv,hV⟩:= inks_treaty a hp h hs x; refine ⟨R _ _ (F x).1 hv hV,fun N hx=>?_⟩
    obtain ⟨hy,hz⟩:= (F x).2 N hx; have he:= genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) _ a h hs hx
    obtain ⟨P,H⟩:= R _ _ hy (Temper.frame he E) (Sane.frame he E)
    obtain ⟨Q,H'⟩:= R _ _ hz (temper_less (Temper.frame he E) hv hy (F x).1 (hp.zero x).le (hp.zero x).le) ((Sane.frame he E).sub hV hy (F x).1 (hp.zero x) (hp.zero x))
    exact ⟨P,Q,H, (mul_right_comm (B x) (shadePrice G E (W.windowD x)) (fare_n x N)) ▸ H'⟩
end costs
end YM.FormalBulk08.Broc
