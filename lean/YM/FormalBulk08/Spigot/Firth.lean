import YM.FormalBulk08.Spigot.Root
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}

lemma stream_lots (p:ℤ): ∃ v:Fin p.natAbs→ℝ×ℤ,(∀ j, |(v j).1|=1∧(v j).2.natAbs≤p.natAbs)∧ ∀ f:ℤ→ℝ,streamline f p=∑ j, (v j).1*f (v j).2:= by
    by_cases h:0≤p
    · refine ⟨fun j=>(1,j.val),fun j=>⟨abs_one,?h⟩,fun f=>?_⟩
      case h => simp [Nat.le_of_lt (Fin.isLt j)]
      have he:=stream_up f p.natAbs; rw [show (p.natAbs:ℤ)=p by omega] at he; simp only [he,one_mul]; rw [Finset.sum_range];
    refine ⟨fun j=>(-1,-(j.val:ℤ)-1),fun j=>⟨by simp,by dsimp; omega⟩,fun f=>?_⟩
    have he:=stream_down f p.natAbs; rw [show -(p.natAbs:ℤ)=p by omega] at he; rw [he]; simp only [neg_mul,one_mul,Finset.sum_neg_distrib]; congr 1; rw [Finset.sum_range]

def glint (f:Cover→ℝ)(U:Pillow)(x:Cover)(i:Axis):=U (x,i)+f x-f (x+step i)
def barge (f:Cover→ℝ)(U:Pillow)(i:Axis)(x:Cover):ℝ:=f (zoom x i 0)+streamline (fun t=> U (zoom x i t,i)) (x i)
lemma barge_pay {U:Pillow}{i x}{z f}{B:ℝ}(h:∀ x,|U x|≤B)(hz:0≤z)(hf:∀ x:Cover,|f x|≤z*size x*B):|barge f U i x|≤ (z+1)*size x*B:= by
    have he : 0≤ B:=(abs_nonneg (U (x,i))).trans (h _)
    refine (abs_add_le ..).trans ?_; rw [add_mul,add_mul,one_mul]; refine add_le_add ((hf _).trans ?_) ((stream_defray _ _ (fun _=>h _)).trans ?_)
    · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hz) he; exact_mod_cast studio_cost x i 0 (Nat.zero_le _)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (studio_amount x i)) he
lemma barge_first (U:Pillow)(i x f):barge f U i (x+step i)-barge f U i x=U (x,i):= by
    have he t:zoom (x+step i) i t=zoom x i t:= by ext1 j; by_cases h:j=i <;>simp [zoom,h]
    simp_rw [barge,he]; change _+streamline _ ((x+step i:Cover) i)-_= _
    rw [show (x+step i:Cover) i=x i+1 by simp,stream_credit, show zoom x i (x i)=x from by simp [zoom]]; ring
lemma barge_grid (U:Pillow)(i j x f)(h:i≠j): glint (barge f U j) U x i=glint f U (zoom x j 0) i+streamline (fun p:ℤ=> beadCurl U (zoom x j p) j i) (x j):= by
    let g(p:ℤ):=glint (barge f U j) U (zoom x j p) i;have he(p):g (p+1)-g p=beadCurl U (zoom x j p) j i:= by
       let u:=zoom x j p; have h₁:=barge_first U j u f; have h₂:=barge_first U j (u+step i) f
       change glint _ U (zoom x j (p+1)) i-glint _ U u i=_; rw [neigh];change glint _ U (u+step j) i-_ = beadCurl _ u _ _
       unfold glint beadCurl; rw [show ∀ z:Axis,u+step j+step z=u+step z+step j by intro;abel]
       linarith
    have hz : g 0=glint f U (zoom x j 0) i:= by
       have ha (v:Cover)(p:v j=0):barge f U j v=f v:= by rw [barge,show zoom v j 0=v by rw [←p]; simp [zoom],p,show ∀ f, streamline f 0=0 from fun f=> by simpa only [Nat.cast_zero,Finset.range_zero,Finset.sum_empty] using stream_up f 0,add_zero]
       unfold g glint; rw [ha _ (update_self ..),ha]; simp [zoom,Ne.symm h]
    have hy:g (x j)=glint (barge f U j) U x i:= by simp [g,zoom]
    rw [←hy, stream_telescope g, hz]; simp_rw [he]

-- homogeneous source lift, displacements controlled in native widths,
-- number of generated terms linear, no path exp assumption afterwards
abbrev Plaque := ℝ × Face ℤ
def dropP (v:Plaque)(U:Pillow):ℝ:= v.1*curlP v.2 U
def Bars (d:ℕ)(v:Fin r→Plaque) :Prop:=∀ i,|(v i).1|=1∧ size (v i).2.1 ≤ d
lemma pool (P:Finset Axis):∃ F:Pillow→Cover→ℝ,(∀ U:Pillow,∀ C,(∀ v,|U v|≤C) → ∀ v, |F U v|≤ P.card*(size v:ℝ)*C)∧ ∀ x i, i∈ P→∃ (n:ℕ)(v:Fin n→Plaque), n≤ P.card*size x∧ Bars (size x) v∧∀ U:Pillow, glint (F U) U x i=∑ j,dropP (v j) U:= by
   induction P using Finset.induction with
   | empty=> exact ⟨fun _ _=>0,by simp,by simp⟩
   | @insert j P h ih=>
     obtain ⟨f,hf,H⟩:=ih;let F(U:Pillow):= barge (f U) U j; simp_rw [Finset.card_insert_of_notMem h, Nat.cast_add, Nat.cast_one]; refine ⟨F,fun _ _ hx _=>barge_pay hx (Nat.cast_nonneg _) (hf _ _ hx),fun x i he=>?_⟩
     rcases Finset.mem_insert.mp he with rfl|he
     · refine ⟨0,Fin.elim0,Nat.zero_le _,fun i=> Fin.elim0 i,fun U=> ?_⟩; have he:=barge_first U i x (f U); rw [Fintype.sum_empty]; unfold glint F; linarith
     let y:=zoom x j 0; obtain ⟨t,v,hv,hx,Hx⟩:=H y i he; let r:=(x j).natAbs
     obtain ⟨V,hV,hR⟩:=stream_lots (x j); have ha:j≠i:=fun e=> h (e.symm ▸ he); obtain ⟨a,z,hz,hP⟩:=weave j i ha
     let p (l:Fin r): Plaque:=((V l).1*z,zoom x j (V l).2,a)
     have hy:size y≤ size x:= studio_cost x _ _ (Nat.zero_le _)
     refine ⟨_,Fin.append v p,(Nat.add_le_add (hv.trans (Nat.mul_le_mul_left _ hy)) (studio_amount x j)).trans_eq (by simp [add_mul]),?_,fun U=>?_⟩
     · refine fun i=>Fin.addCases ?_ ?_ i
       · intro i; rw [Fin.append_left]; exact ⟨(hx i).1,((hx i).2.trans hy)⟩
       intro i; rw [Fin.append_right]; exact ⟨by dsimp [p]; rw [abs_mul,hz,(hV i).1,one_mul],studio_cost x j _ (hV i).2⟩
     rw [Fin.sum_univ_add, barge_grid U i j x _ ha.symm,Hx,hR]; simp only [dropP,p,Fin.append_left, Fin.append_right, mul_assoc,hP]; rfl
end YM.FormalBulk08.Spigot
