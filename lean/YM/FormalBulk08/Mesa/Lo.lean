import YM.FormalBulk08.Mesa.Main

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {I : Type*} {r : ℕ}
lemma pair_bank (n : Side) (R : Row I I) : cum 0 n (couple (lands R))=couple (R.acts n) := by
   funext v
   let a := boil n (v 0); let b:=v 1
   let P := Picks 0 n a v; let U := {x:Cover| b.1= wrap n a.1+ wrap n x} -- replace
   let f (w : P):= (w.val 1).1-(w.val 0).1
   have hp (w : P) (i) : drip n (w.val i)=v i:= congr_fun w.property.2 i
   have he (w:P) : f w∈U := by
      unfold f;rw [w.property.1];have ht:b.1=_ := (congr_arg Prod.fst (hp w 1).symm);change b.1=wrap n a.1+wrap n _; rw [map_sub];exact ht.trans (by change wrap n (w.val 1).1= _; abel)
   let g : P→ U:= fun w=>⟨f w,he w⟩
   have h : Bijective g := by
      constructor
      · intro x y h;have hv : f x=f y:=congr_arg Subtype.val h
        apply Subtype.ext; funext i; have he : i=0 ∨ i=1:=by omega
        rcases he with he|he <;> subst i
        · exact x.property.1.trans y.property.1.symm
        have ht : (drip n (x.val 1)).2=(drip n (y.val 1)).2 := congr_arg Prod.snd ((hp x 1).trans (hp y 1).symm)
        unfold f at hv; rw [x.property.1,y.property.1] at hv; exact Prod.ext (sub_left_inj.mp hv) ht
      intro x; let w : chain (Biglot I) 2 := ![a,(a.1+x.val,b.2)]
      have hW : drip n ∘ w = v := by
         funext i; have he : i=0 ∨ i=1:=by omega
         rcases he with he|he <;> subst i
         · simp [w,a]
         change _=b; apply Prod.ext
         · change wrap n (a.1+x.val)= _;rw [map_add]; exact x.property.symm
         rfl
      exact ⟨⟨w,rfl,hW⟩,Subtype.ext (by simp [g,f,w])⟩
   let A i:= -halve (R (v 0).2 b.2 i); let e := Equiv.ofBijective g h
   have hh : (∑' w:P,couple (lands R) w.val) = ∑' u : Cover, if u∈U then A u else 0:= by
      rw [show (fun u:Cover=> if u∈U then A u else 0)=U.indicator A from (funext fun z=>by simp only [Set.indicator]; split_ifs <;> rfl),←tsum_subtype, ←Equiv.tsum_eq e]; refine tsum_congr fun w=>?_ ;
      have h0 : (w.val 0).2=(v 0).2 := (show (drip n (w.val 0)).2=(v 0).2 from congr_arg Prod.snd (hp w 0)); have h1: (w.val 1).2=b.2:= (show (drip n (w.val 1)).2=(v 1).2 from congr_arg Prod.snd (hp w 1))
      unfold couple lands;rw [h0,h1];rfl
   change (∑' w:P,couple (lands R) w.val) = -halve (∑' i,if b.1=(v 0).1+wrap n i then R (v 0).2 b.2 i else 0)
   rw [hh,halve,←tsum_mul_left,←tsum_neg]; refine tsum_congr fun i=>?_;simp [A,U,a,b,boil,halve, apply_ite]; split_ifs <;> simp_all
lemma setkin_folds (G : Gauge) {η b : ℝ} (R : Row (TypeFace 2) (TypeFace 2)) (hn : 0 ≤η) (hb : 0≤b) (h : R.strip η b) (n : Side) (i : Fin 2) :
      cum i n (setkin G R)=marble 2 (crunch (patron G (Precision.K (R.acts n)))) := by
   obtain ⟨C,hC,H⟩:=ink_charge G _ hn
   obtain ⟨hv,hg⟩:=H R b hb h
   rw [kinetic_marble,←hg];unfold setkin;rw [cum_sand i n hn (peg_charge hv (mul_nonneg hC hb)) (up_couple _), ←pair_bank]
   congr 1; funext v;rw [cum_root i 0 n _ _ (up_couple _)]
lemma cum_cmp {T Z : Tile (Biglot I) r} (u : Up T) (v : Up Z) (η ξ C B) (h : 0≤η) (hx : 0 ≤ ξ) (hu : Bail (fame I) η T C) (hv : Bail (fame I) ξ Z B) (i : Fin r) (he : ∀ n,cum i n T=cum i n Z) : T=Z := by
   refine lights_unique (R:=fun n=>cum i n Z) ?_ (spark Z i hx hv v);simp_rw [←he]; exact spark T i h hu u
end YM.FormalBulk08.Mesa
