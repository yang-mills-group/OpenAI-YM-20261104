import YM.Contacts.Harrier.Cup
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
section weights
variable {Y Z: Ribbon X k}{x:X}{U: Finset α} {l : Pulse.Range (Node X)}
lemma w_scale (h:Weight Y D l x b)(a:ℝ): Weight (a • Y) D l x (‖a‖*b) := fun f v hv he=> mul_assoc ‖a‖ b v|>.symm ▸ ((h f v hv he).smul a)
lemma w_add (h:Weight Y D l x b)(hp:Weight Z D l x c): Weight (Y+Z) D l x (b+c):= fun f v hv he=> add_mul b c v|>.symm ▸ ((h f v hv he).add (hp f v hv he))
lemma w_sub (h:Weight Y D l x b)(hp:Weight Z D l x c): Weight (Y-Z) D l x (b+c):= fun f v hv he=> add_mul b c v|>.symm ▸ ((h f v hv he).sub (hp f v hv he))
lemma w_sum {B:α→Ribbon X k}{b:α→ℝ}(h:∀ i∈U,Weight (B i) D l x (b i)): Weight (∑ i∈U,B i) D l x (∑ i∈U,b i):= by
   intro f v hv he; rw [sum_mul,Finset.sum_apply]; exact Rest.sum (fun j hj=> h j hj f v hv he)
lemma w_zero : Weight (0:Ribbon X k) D l x 0:= by intro f v hv he; change Rest _ _ 0 _; rw [zero_mul]; apply Rest.zero
lemma w_upped {t:Pulse.Range (Node X)}(h:Weight Y D l x b)(he:b≤c)(hg: ∀ f:Option (Fin k)→ _, t.bill f ≤ l.bill f) : Weight Y D t x c:= fun v s hs hw=> (h v s hs hw).upto _ hg (mul_le_mul_of_nonneg_right he hs)
lemma w_raise (h:Weight Y D l x b)(he:b≤c): Weight Y D l x c := w_upped h he fun _=>le_rfl
lemma w_lower (h:Weight Y D (terrain σ X) x b)(he:ζ≤σ): Weight Y D (terrain ζ X) x b:= w_upped h le_rfl (terrain_le he)
lemma w_hole (h:Weight Y D l x 0): Y=0:= by funext B v; obtain ⟨b,hb,hB⟩:=Cards.reach D B; have hx:=h B b hb hB; rw [zero_mul] at hx; exact norm_le_zero_iff.mp (budget_single hx.raw v)
end weights
-- keep root-level puncture as a linear functional on Cards. Membership requires no analytic behavior in actual coupling. Absolute moment prices through a fixed profile order D.
abbrev Sketch (G: Gauge):= Cards → bore G
abbrev sail (K:Sketch G)(i j:ℕ) : Ribbon (Dye G) j:= fun s=> K s i j
variable (y:Dye G)(M D:ℕ) {V P:Sketch G}
structure Living (K: Sketch G)(ζ:ℝ≥0): Prop where
    lin: IsLinearMap ℝ K
    lineage: ∀ v,Based ζ y M (K v)
    budget i j : ∃ b≥(0:ℝ), Weight (sail K i j) D (terrain ζ (Dye G)) y b
namespace Living
variable {y M D}
lemma member (h:IsLinearMap ℝ P)(hp:∀ i j,∃ b≥(0:ℝ),Weight (sail P i j) D (terrain ζ _) y b)(he:∀ v,Mount (P v) M): Living y M D P ζ:= by
   refine ⟨h,fun v=> ⟨he v,?_⟩,hp⟩; obtain ⟨s,hs,hS⟩:= Cards.reach D v; choose p _ h using hp; exact ⟨fun i j=>p i j*s,⟨fun i j=> h i j v s hs hS⟩⟩ -- scalar price choice
lemma zero (y:Dye G)(M D:ℕ):Living y M D 0 ζ := ⟨⟨by simp,by simp⟩,fun _=> Based.zero,fun _ _=> ⟨_,show 0≤(0:ℝ) from le_rfl,w_zero⟩⟩
lemma add (h:Living y M D P ζ)(ht:Living y M D V ζ): Living y M D (P+V) ζ:= ⟨⟨fun _ _=>by simp [h.lin.map_add,ht.lin.map_add,add_add_add_comm],fun _ _=>by simp [h.lin.map_smul,ht.lin.map_smul,smul_add]⟩, fun v=> Based.add (h.lineage v) (ht.lineage v),fun i j=> by obtain ⟨b,hb,hB⟩:=h.budget i j; obtain ⟨c,hc,hC⟩:=ht.budget i j; exact ⟨_,add_nonneg hb hc,w_add hB hC⟩⟩
lemma scale (h:Living y M D P ζ)(a:ℝ): Living y M D (a • P) ζ:= ⟨⟨fun _ _=> by simp [h.lin.map_add, smul_add],fun r _=> by simp [h.lin.map_smul,smul_comm r a]⟩, fun v=> Based.smul (h.lineage v) a, fun i j=> by obtain ⟨b,hb,h⟩:=h.budget i j; exact ⟨_,mul_nonneg (norm_nonneg a) hb, w_scale h a⟩⟩
lemma lower (h:Living y M D P σ)(H:ζ≤σ): Living y M D P ζ:= by refine member h.lin ?_ (fun v=> (h.lineage v).1); intro i j; obtain ⟨p,hp,h⟩:=h.budget i j; exact ⟨p,hp,w_lower h H⟩
end Living
def Area (y:Dye G) (M D:ℕ) (ζ:ℝ≥0) : Submodule ℝ (Sketch G) where
    carrier:=fun F=>Living y M D F ζ
    zero_mem':= Living.zero _ _ _
    add_mem' _ _:= Living.add ‹_› ‹_›
    smul_mem' a _ ht:= Living.scale ht a
namespace Living
variable {y M D}
lemma sum {V:A→ Sketch G}(p:Finset A) (h:∀ i∈p,Living y M D (V i) ζ) : Living y M D (∑ i∈p,V i) ζ:= (Area ..).sum_mem h
lemma neg (h:Living y M D P ζ): Living y M D (-P) ζ:= (Area y M D ζ).neg_mem h
lemma sub (h:Living y M D P ζ)(H:Living y M D V ζ): Living y M D (P-V) ζ:= (Area y M D ζ).sub_mem h H
-- locality of heritage proof. enables constructing auxiliary-corrected fields as all-order formal series
lemma closed (h:∀ q:ℕ, ∃ F:Sketch G, Living y M D F ζ ∧ ∀ φ i,i ≤ q→ V φ i=F φ i) : Living y M D V ζ:= by
    choose Y hp hh using h; have hv (s:Cards)(i:ℕ): V s i=Y i s i:= hh i s i le_rfl; refine ⟨⟨fun _ _=>?_ ,fun v z=>?_⟩,fun v=>Based.capacity (fun k=>⟨_,(hp k).lineage v,hh k v⟩),fun i j=> ?_⟩
    · ext1 i; rw [hv,(hp i).lin.map_add]; simp only [Pi.add_apply,hv]
    · ext1 i; rw [hv,(hp i).lin.map_smul]; simp only [Pi.smul_apply,hv]
    rw [show sail V i j=_ from (show _=sail (Y i) i j from funext fun B=> congr_fun (hv B i) j)]; exact (hp i).budget i j
end Living
end
end YM.Contacts.Harrier
