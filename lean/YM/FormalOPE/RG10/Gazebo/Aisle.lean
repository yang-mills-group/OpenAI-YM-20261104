import YM.FormalOPE.RG10.Gazebo.Tents
/-! Nested real-frame Lie shifts via zero padding and restriction in the actual coherent Deck.
H rotation proved for these; filtration all through d. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open RG10.Position RG10.Position.Grade Deck Shutters
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d k:ℕ}(h:d≤k)
local notation "f"=> climb F h
local notation "𝓥" d=> Deck F d
local notation "𝓕" d=> FrameAt (Deck F d) ℝ
local notation "𝒩" d=> tents F d
local notation "S" k s=> RG10.Position.Grade.swing (F:=F) k s

abbrev π : (𝓕 k) →ₗ[ℝ] 𝓕 d:= { toFun:= clip f, map_add':= fun _ _=> rfl,map_smul':= fun _ _=>rfl }
lemma branch_grade (s:Signed): clip f (swing (F:=F) k s)=swing (F:=F) d s:= by
 let b:= deck F d; let B:= deck F k; funext i j; apply Complex.ofReal_injective
 change (↑((swing (F:=F) k s) (f i) (f j)):ℂ)= _; rw [swing_deck, ← cabin, ride_high,swing_deck]; -- issue cabin at i or j
 let x:= ride F s.ortho d (b i); nth_rw 1 [← (deck F d).sum_repr (ride F s.ortho d (deck F d i))];
 simp_rw [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply, cabin, Module.Basis.repr_self, Finsupp.single_apply]
 simp [-deckAt, (Deck.climb_inj F h).eq_iff]

private lemma atRight' {i:𝓥 k} : i∈Set.range f ↔ Deck.price F k i≤d:=by constructor; rintro ⟨i,rfl⟩; exact Deck.price_bound F d i; exact Deck.of_price F h
lemma no_pass {A: Matrix (𝓥 k) (𝓥 k) ℝ} (ht:Cut (Deck.price F k) A) : lowers f A:= fun i j hv=> ht (f i) j (lt_of_le_of_lt (Deck.price_bound F d i) (lt_of_not_ge ((atRight' h).not.mp hv)))
-- FrameReal version cut plugging all matrices.T.C.Use for Bindings.L.
private lemma clip_mul {A : Matrix (𝓥 k) (𝓥 k) ℝ} (B : Matrix (𝓥 k) (𝓥 k) ℝ)(ht:lowers f A) : of (clip f (A*B))= of (clip f A)* of (clip f B):= by
 ext i j; simp only [of_apply,clip,Matrix.mul_apply]
 let C (a:𝓥 k):= A (f i) a * B a (f j)
 change ∑ j,C j=∑ a,C (f a)
 conv_rhs=> rw [← sum_image («f»:=C) (by exact (Deck.climb_inj F h).injOn)]
 symm; refine sum_subset (subset_univ _) (fun i _ hh=> ?_); unfold C; rw [ht _ i (by simpa using hh),zero_mul]

lemma transfers {A : 𝓕 k}(ht:A∈𝒩 k) : clip f A∈𝒩 d:=by
 obtain ⟨⟨he,hs⟩,hb⟩:= (and_congr_left fun _=> votes _).1 ((pinned A).1 ht)
 refine ⟨(votes _).2 ⟨fun i j hv=> he (f i) (f j) hv, fun s=>?_⟩, funext fun i=> by unfold clip; rw [show f (Deck.start F d)=Deck.start F k from rfl,hb]; rfl⟩
 have hh : Cut (Deck.price F k) (swing (F:=F) k s):= Grade.layer_cut (swing_grade _ _); have hu : of (clip f (swing (F:=F) k s))=swing (F:=F) d s:=by rw [branch_grade]; rfl
 change of (clip f (of A))*_= _*of (clip f (of A)); rw [←hu, ← clip_mul h _ (no_pass h he), ←clip_mul h _ (no_pass h hh), hs]

def ρ : (𝒩 k) →ₗ[ℝ] (𝒩 d):= (π h).restrict (show _≤(𝒩 d).comap (π h) from fun _ hw=> transfers h hw)

def puff (A:𝓕 d)(i j:𝓥 k) := if hi:i∈Set.range f then if hj:j∈Set.range f then A hi.choose hj.choose else 0 else 0
lemma landing (A:𝓕 d): clip f (puff h A)=A:= by
 funext i j; let z (i:𝓥 d):f i∈Set.range f:= Set.mem_range_self _; unfold clip puff; rw [dif_pos (z i),dif_pos (z j),(Deck.climb_inj F h) (z i |>.choose_spec),(Deck.climb_inj F h) (z j|>.choose_spec)]
private lemma extension (A:𝓕 d)(ht:A∈𝒩 d): puff h A∈𝒩 k:= by
 obtain ⟨⟨he,hs⟩,hu⟩:= (and_congr_left fun _=> votes _).1 ((pinned A).1 ht)
 let a:Matrix (𝓥 k) (𝓥 k) ℝ:= of (puff h A); have hz i (hi:i∉Set.range f) j : a i j=0:= dif_neg hi
 have hz' j (hj:j∉Set.range f) i : a i j=0:= by unfold a puff; rw [Matrix.of_apply]; split <;> simp_all
 have Ha i j : a (f i) (f j)=A i j:= congr_fun₂ (landing h A) i j
 have hw : Cut (Deck.price F k) a:= by
   intro i j h; by_cases hh : i∈Set.range f; swap; exact hz i hh j
   by_cases h' : j∈Set.range f; swap; exact hz' j h' i
   obtain ⟨i,rfl⟩:=hh; obtain ⟨j,rfl⟩:=h'; rw [Ha]; exact he i j h
 refine ⟨(votes _).2 ⟨hw,fun s=>?_ ⟩, funext fun i=>by
   change a _ i=0; by_cases ht:i∈ Set.range f; swap; exact hz' i ht _
   obtain ⟨i,rfl⟩:=ht; rw [← show f (Deck.start F d)=Deck.start F k from rfl, Ha,hu]; rfl⟩
 let H:=(swing (F:=F) k s); have hh : Layer (Deck.price F k) H:= swing_grade k s; change a*H=H*a; ext i j
 have hE : lowers f a:= no_pass h hw; have hB:= no_pass h (Grade.layer_cut hh)
 have h' i j (hu':j∉Set.range f) : H j (f i)=0:= hh j (f i) (ne_of_gt (lt_of_le_of_lt (Deck.price_bound F d i) (lt_of_not_ge ((atRight' h).not.mp hu'))))
 by_cases hi : i∈Set.range f <;> by_cases hj:j∈Set.range f
 · obtain ⟨i,rfl⟩:=hi; obtain ⟨j,rfl⟩:=hj; have hu : of (clip f a)= of A:= by change of (clip f (puff h A))=_; rw [landing]
   have hv: of (clip f H)=swing (F:=F) d s:=by rw [show clip f H = _ from branch_grade h s]; rfl
   have hd:of (clip f (a*H))= of (clip f (H*a)):= by rw [clip_mul _ _ hE,clip_mul _ _ hB,hv,hu,hs]
   exact congr_fun₂ hd i j
 · change (a*H) i j =  _; rw [mul_apply,mul_apply,sum_eq_zero (fun y _=> mul_eq_zero_of_right (H i y) (hz' j hj y))]
   obtain ⟨i,rfl⟩:=hi; apply sum_eq_zero; intro y _; by_cases h:y∈Set.range f; swap; rw [hz' y h,zero_mul] -- careful zero_mul
   obtain ⟨y,rfl⟩:=h; rw [hB _ _ hj,mul_zero]
 · rw [mul_apply,mul_apply,sum_eq_zero (fun y _=> mul_eq_zero_of_left (hz i hi y) _)]; symm; apply sum_eq_zero; intro y _; by_cases hu:y∈Set.range f; swap; rw [hz y hu,mul_zero]
   obtain ⟨y,rfl⟩:=hu; rw [h' _ _ hi,zero_mul]
 rw [mul_apply,mul_apply,sum_eq_zero (fun y _=> mul_eq_zero_of_left (hz i hi y) _),sum_eq_zero (fun y _=> mul_eq_zero_of_right _ (hz' j hj y))]

def σ : (𝒩 d) →ₗ[ℝ] (𝒩 k) where
 toFun a:= ⟨puff h a.val,extension h a.val a.property⟩
 map_add' x y:= Subtype.ext (by ext i j; change puff h (_+_) i j=puff h _ i j+puff h _ i j; unfold puff; split_ifs <;> simp)
 map_smul' x y:= Subtype.ext (by ext i j; change puff h (x • (y.val)) i j=x * puff h _ i j; unfold puff; split_ifs <;> simp)
lemma marches (i:𝒩 d) : ρ h (σ h i)=i:=Subtype.ext (landing h i.val)

def mode (d:ℕ) : (𝒩 d)→ₗ[ℝ] 𝒩 d := (glazed (Deck.slots F d)).restrict (show _ ≤ (𝒩 d).comap _ from fun _ h=> tenant _ h)
lemma mode_two (i:𝒩 d): mode d (mode d i)=i := Subtype.ext (glass_swap (Deck.slots F d) i.val)
lemma catch_rising (x:𝒩 d) : mode k (σ h x)= σ h (mode d x):= Subtype.ext (by
 ext i j; change glass (Deck.slots F k) (puff h _) i j=puff h (glass (Deck.slots F d) _) i j; unfold glass
 by_cases hi:i∈Set.range f <;> by_cases hj:j∈Set.range f
 · obtain ⟨i,rfl⟩:=hi; obtain ⟨j,rfl⟩:=hj; change lapse («S»:=ℝ) _ * clip f (puff _ _) i j= clip f (puff _ _) i j; rw [landing,landing]; rfl
 all_goals simp only [puff, hi, hj, ↓reduceDIte, mul_zero])
lemma catch_falling (x:𝒩 k) : mode d (ρ h x)= ρ h (mode k x):= rfl
end YM.FormalOPE.RG10.Gazebo
