import YM.Contacts.Procession.Scarab
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration
open Milling Milling.Steam Milling.Forge Pulse.Form
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {α β ι T : Type}{g:Gauge}{σ:ℝ≥0}{b c:ℝ}{u h i k:ℕ} (m:Side) [AddCommGroup T]
local notation "M"=>Node (Option α)
local notation "Ym"=>Co m (Option α)
variable {F:Field (Fin i) (Node α)}
lemma focus_root (x v: Boys i (T×α))(y y':T)(h:focus y x=focus y' v): y=y'∧ x=v:= Prod.mk.inj ((scroll T α i).injective h)
lemma bent_f (x:Cover)(q:Boys i (Node α)): lower m ∘ focus x q=focus (wrap m x) (lower m ∘ q):= by
   funext j; refine Fin.cases ?_ (fun i=>?_) j; · rfl
   exact Prod.ext (map_add (wrap m) _ _) rfl
private lemma orbit_spec (x:Boys (i+1) M) : x∈Set.range (scroll Cover α i) ↔ lower m ∘ x∈Set.range (scroll (Site m) α i) := by rw [scar_species,scar_species]; rfl
-- Extract relative rooting at Mark. Works regardless of r=0.
variable (x:Cover)(v:Boys i (Co m α))
private abbrev P := {p:Boys i (Node α)// lower m ∘ p=v} -- add variable args implicitly?
private abbrev Q := {p:Locked M (0:Fin (i+1)) (x,none)// lower m ∘ p.val=focus (wrap m x) v}
def dent (m:Side)(x:Cover)(v:Boys i (Co m α))(y:P m v) : Q m x v:= ⟨⟨focus x y.val,rfl⟩,(bent_f m x _).trans (congr_arg (focus _) y.property)⟩ -- private binder m naming
private lemma dent_total : Bijective (dent m x v):= by
   refine ⟨fun a b h=>Subtype.ext ((focus_root _ _ x x (congr_arg (fun p:Q m x v=> p.val.val) h)).2),fun ⟨y,hy⟩=>?_ ⟩; let t:=focus (wrap m x) v; obtain ⟨⟨a,b⟩,h⟩: y.val∈ (Set.range (scroll Cover α i)) := (orbit_spec m y.val).2 (hy.symm ▸ (show t ∈ _ from ⟨(wrap m x,v),rfl⟩))
   change focus a b=_ at h; obtain rfl : a=x:= congr_arg Prod.fst ((congr_fun h 0).trans y.property); rw [←h,bent_f] at hy -- dependent rw?
   exact ⟨⟨b,(focus_root _ _ _ _ hy).2⟩,Subtype.ext (Subtype.ext h)⟩
lemma shade {F:Field (Fin (i+1)) M} {V:Field (Fin (i+1)) Ym} (h:Shadow (lower m) F V) : V (focus (wrap m x) v)= packing (lower m) (fun p=> F (focus x p)) v:= by
   rw [h.rule _ 0 (x,none) rfl]; let f:= Equiv.ofBijective _ (dent_total m x v); exact (f.tsum_eq _).symm
lemma beyond (F:Field (Fin i) (Node α)): Shadow (lower m) (scarab F) (scarab (packing (lower m) F)):= by
   let p:=lower (α:=Option α) m; let A:=scarab F; let G:= printShadow A m; let V:= (scarab (packing (lower m) F)); have h:Shadow p A G:= printFeeds (heritage (fun i x=> scar_shift F i x) m); suffices v : G=V from (show Shadow p A V from v ▸ h)
   funext x; by_cases hx:x∈ Set.range (scroll (Site m) α i)
   · obtain ⟨⟨a,b⟩,rfl⟩:=hx; let x:=focus a b; let z:=lift a; change G x=V x; unfold x; rw [←wrap_lift a, shade m (lift a) b h]; unfold V A; rw [scar_read]; simp_rw [scar_read]
   obtain ⟨y,hy⟩:= lower_onto m (x 0); rw [h.rule x 0 y hy]; unfold V scarab Lay; rw [dif_neg hx]; refine (tsum_congr ?_).trans (tsum_zero (α:=ℝ)); intro v; exact dif_neg (fun he=>hx (v.property ▸ (orbit_spec m v.1.val|>.mp he))) -- nested lift property card
lemma peel_root (x:T)(v:Boys i (T×α)): focus x v 0=(x,none):=rfl
def scoop (v:Field (Fin (i+1)) (Live T α)): Field (Fin i) (T×α):= (i+1:ℕ) • fun p=>v (focus 0 p)
lemma homing_credit {F:Field (Fin (i+1)) M}{v:α}(h:Rooted (terrain σ _) F b): Rest (terrain σ α) (0,v) (scoop F) ((i+1:ℕ)*b):= by
   let x:M:=(0,none); let e (v:Boys i (Node α)): Locked M (0:Fin (i+1)) x:= ⟨focus 0 v,rfl⟩; let f (v:Boys i (Node α)):= F (focus 0 v); have hl:Rest (terrain σ α) (0,v) f b:= budget_map (h.row 0 x) _ (show Injective e from fun a b h=> (focus_root _ _ (0:Cover) _ (congr_arg Subtype.val h)).2) (fun i=>congr_arg _ (playBill i 0 v).symm); convert hl.smul ((i+1:ℕ):ℝ) using 1; · ext1 v; change _= (↑(_) :ℝ) * f v; rw [scoop, Pi.smul_apply,nsmul_eq_mul]
   congr 1; exact (Real.norm_of_nonneg (by positivity)).symm
lemma home {F:Field (Fin (i+1)) M} {v: Field (Fin (i+1)) Ym} (h: Shadow (lower m) F v) : scoop v = packing (lower m) (scoop F) := by
    ext1 x; unfold packing scoop cram; rw [Pi.smul_apply, show (0:Site m)= wrap m 0 from ((wrap m).map_zero).symm, shade m (0:Cover) x h]; simp_rw [Pi.smul_apply, nsmul_eq_mul,tsum_mul_left]; rfl
end YM.Contacts.Procession.Xenon
