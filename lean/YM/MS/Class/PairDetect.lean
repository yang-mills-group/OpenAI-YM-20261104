import YangMills.WilsonProof.NativeSupport.YM.MS.Class.Kinetic
/-!
# Two-leg classification assembled

The real scalar pieces, identity on all colors. If lower dimension no rank 2.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau.Detect
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Mark
open scoped Topology ContDiff InnerProductSpace
open Complex (I)
variable {G:Gauge} {F H : Law G} {h:ℤ}

-- `a` for kinetic, `b` for anti-c. Factor includes no color trace normalization.
def kinds (a b:ℝ) : Atom Axis → Atom Axis → FourP → ℂ
| (some i,false),(some j,false),p=> (precision i j p:ℂ)*(a:ℂ)
| (none,false),(some i,true),p=> (b:ℂ)*I*(p i:ℂ)
| (some i,true),(none,false),p=> (b:ℂ)*I*(p i:ℂ)
| _,_,_=>0

def ranktwo (a b:ℝ) : Law G
| [l,r] => if l.1.2=r.1.2 then kinds a b l.1.1 r.1.1 l.2 else 0
| _=> 0

lemma color_ne (K:G.Simple) : Nonempty (CI G) := by
    haveI := K.nontrivial_color
    exact ⟨⟨0,by rw [Gauge.lieDim,← G.colorIso.finrank_eq]; exact Module.finrank_pos⟩⟩
-- pointwise tested; independent of other ranks. `Ranked` lets one read this as total kernel identity.
def EqualAt {A:Type} (r:ℕ) (F H : Row A FourP ℂ) : Prop := ∀ w, net w=0 → w.length=r → F w=H w

lemma pair_class (X:Class F h) (K:G.Simple) (H:h≤4) : ∃ a b, (h=4 ∨ a=0 ∧ b=0) ∧ EqualAt 2 F (ranktwo a b) := by
   obtain ⟨e⟩:= color_ne K
   obtain ⟨a,ha,hA⟩:= spectrum e e X H; obtain ⟨b,hb,hB⟩:= ghost_scalar e e X H
   refine ⟨a,b,by tauto, fun w hs hu=>?_⟩
   obtain ⟨l,r,rfl⟩ := List.length_eq_two.mp hu
   rcases l with ⟨⟨l,i⟩,p⟩; rcases r with ⟨⟨r,j⟩,q⟩; have hx : q= -p:= by simpa [net,add_eq_zero_iff_eq_neg',eq_comm] using hs
   subst q
   change F [qnote l i p,qnote r j (-p)]=_
   rw [pair_color X K l r p e i j,ranktwo]; dsimp only; split_ifs with hθ
   · rcases l with ⟨_|l,_|_⟩ <;> rcases r with ⟨_|r,_|_⟩
     all_goals first | exact hA _ _ _ | exact hB _ _ | skip
     all_goals first |  (solve | (refine X.ne _ hs ?_; norm_num [fieldDim,qnote,ghostNo,ghostChannel]))| skip
     -- last anti ghost
     have ht:= X.swap [] (U l e p) (C e (-p)) [] hs
     simp only [List.nil_append] at ht
     rw [show [qnote (some l,true) e p,qnote (none,false) e (-p)]=_ from rfl, ht]; change -1* F [C e (-p),U l e p]=_ -- trace
     have hl : F [C e (-p), U l e p]=(b:ℂ)*I*((-p) l:ℝ):= by simpa only [ghostPair,neg_neg] using hB l (-p)
     rw [hl]; simp [kinds]
   rfl
end YM.MS.Landau.Detect
