import YM.OPE.Backup.Recast
/-! # Retrieval for a discrepancy against exact fields at the same position -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster.Pigment
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open scoped Topology BigOperators Classical
variable {I J V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype V][DecidableEq V]{G:Gauge}{n:Side}
local notation "X"=> (Names V I)
local notation "Y"=> (Names V J)
variable (A:I→J) (s:V×I→ℂ){R:Rep G n}
set_option quotPrecheck false
variable {w:V×I→ℝ} {w':V×J→ℝ}{y x z:ℝ}
def sweep (V:Type) (A:I→J) : V×I→V×J:= Prod.map id A
local notation "f"=> sweep V A
local notation "F"=> homL f s
lemma focus_preserved (p:(Names V I).Mode) (v:V) : Focused v p ↔ Focused v (batch f p):= by
   unfold Focused homes; change p.val.image Prod.fst⊆_ ↔ ((p.val.image f).image Prod.fst) ⊆ _; rw [image_image]; rfl
lemma pallor (u:(X).Mode){a:Equiv.Perm V}{v:V}{m:Motion} (hs:∀ i:I,s (a v,i)= scalar m (s (v,i))) : Harm v a m (mark f s u) (mark f s (drum a u)):=by
    unfold mark; rw [drum,pares,Finset.prod_image]; swap; · exact (nome a).injective.injOn
    refine Harm.prod_ _ _ _ fun i _=>?_ ; let q:= f i; let q' := f (nome a i)
    by_cases hp:i.1=v
    · rw [show f (nome a i)=nome a q from rfl, show s (nome a i)= scalar m (s i) from ?_]; refine ?_; rotate_left
      · cases i; dsimp only at hp ⊢; subst v; exact hs _
      rw [← go_one]; exact Harm.solo ((Y).fire q) (s i)
    intro p hp'; have hx:p ≠ (Y).fire q:=fun he=>hp ((which v q).mp (he ▸ hp')); change (Poly.send ((Y).fire (nome a q)) _).part _= scalar m ((Poly.send ((Y).fire q) _).part _); simp only [← go_one,Poly.part_send,Equiv.apply_eq_iff_eq,hx,if_false,scalar_z]
lemma theme {p q:Poly X}{a:Equiv.Perm V}{v:V}{m:Motion}(hp:Harm v a m p q) (hs:∀ i:I,s (a v,i)= scalar m (s (v,i))) : Harm v a m (F p) (F q):=by
    intro i hi; rw [part_of,part_of, ← Equiv.sum_comp (drum (slotsZ:=I) a),← scales]; refine sum_congr rfl fun j _=>?_ ; by_cases he:Focused v j
    · rw [hp j he,scalar_mul,pallor A s _ hs i hi]
    have hk : (mark f s j).part i=0:=not_not.mp (fun h=> he ((focus_preserved A j v).2 ((remembered f s j h).2.1 ▸ hi)))
    rw [hk,pallor A s _ hs i hi,hk,scalar_z,mul_zero,mul_zero,scalar_z]
lemma parcelled {q:V→ Site n}{b:V→ Equiv.Perm V}{v:V}{E:V→Motion}
   {H:Support n→ Config G n→Poly X}{K:Box n→ Config G n→Poly X}(h:Horn v E q b H K) (ht:∀ i,i≠v→∀ j:I,s ((b i) v,j)= scalar (E i) (s (v,j))): Horn v E q b (fun i=> F ∘ H i) (fun i=> F ∘ K i):= fun i hi=>⟨(h i hi).1,fun U=>⟨fun j=>theme _ _ (h i hi|>.2 U|>.1 j) (ht i hi),fun j=>theme _ _ (h i hi|>.2 U|>.2 j) (ht i hi)⟩⟩
variable {o:V×I→Site n}{o':V×J→Site n}{u:V→Site n}
variable {q:Config G n→Poly (Names V I)}{v:V}{E:V→Motion}{B:V→ Equiv.Perm V}
variable {α:V×I→ Config G n→ℂ}{β:V×I→Res G n}{L:Ward (Names V I)}{K:Ward (Names V J)}
def palette {M:Type*}[AddCommMonoid M][SMul ℂ M] (q:V×I→ M) (j:V×J):= ∑ i∈ residents A j.2,s (j.1,i) • q (j.1,i)
lemma folkloric (M:Type*) [AddCommMonoid M] (t:V×I→ M)(j:V×J): (∑ i∈ residents f j,t i) = ∑ i∈ residents A j.2,t (j.1,i):=by
    unfold residents; simp only [sum_filter]; rcases j with ⟨j,a⟩; rw [Fintype.sum_prod_type]; simp only [sweep,Prod.map_apply,id_eq,Prod.mk.injEq,ite_and]; rw [sum_eq_single j]; · simp
    · intro b hb hf; simp [hf]
    simp
lemma coats (h:Bard R L v E B u o α β q w y)
    (hO:∀ i,s i ≠ 0 → o' (f i)=o i)
    (hS:∀ i,w' (f i)*‖s i‖≤w i)(hx:∀ i,0≤w' i)(hw:∀ i,0 ≤ w i)
    (ht:∀ i:V,i≠v→∀ j:I,s (i,j)= scalar (E i) (s (v,j)))
    (hh:∀ i:(Names V I).Mode,K.ready (batch f i)→ Set.InjOn f i.val → (∀ j∈i.val,s j ≠ 0) →L.ready i): Bard R K v E B u o' (palette A s α) (palette A s β) (F ∘ q) w' y:=by
    obtain ⟨Y',hs,hL⟩:=h.grants; obtain ⟨H,Q,hT,hW,hZ,hP,he⟩:=hs; refine ⟨F ∘ Y',⟨(fun i=> F ∘ H i),(fun i=>F ∘ Q i),cartonL _ _ hO hT, TowedL _ _ hW hS hx hw, TowedL _ _ hZ hS hx hw, parcelled _ _ hP (fun i hi=> by rw [(hP i hi).1]; exact ht _ hi),?_⟩,fun U=> matching _ _ _ _ (q U) (Y' U) (hL U) hh⟩
    funext i; simp only [he,comp_apply]; rw [restoreL _ _ _ H Q α β i (fun j=> (hT.exp j).1.sil i)]; unfold palette; simp_rw [show ∀ i:V×J, (∑ j∈ residents f i, s j • α j) = _ from fun i=> folkloric A _ (fun j=>s j • α j) i, show ∀ i:V×J, (∑ j ∈ residents f i,s j • β j)= _ from fun i=> folkloric A _ (fun j=>s j • β j) i]
lemma born_with (F':V×I→ Config G n→ℂ) (R:Rep G n) (U:Config G n) : F (birth X R F' U)=birth Y R (palette A s F') U:=by
   unfold birth; rw [map_smul,passes f s _ (mute _ _),MachL]; congr 3; -- edit
   funext j; unfold palette; rw [Finset.sum_apply]; exact folkloric A ℂ (fun i=>s i*F' i U) j
end YM.MergeProof.Ribbons.ManyCopies.Muster.Pigment
