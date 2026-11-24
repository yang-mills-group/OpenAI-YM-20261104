import YM.AlbaMS.Odom.Echo

/-!
# quotient master at its root. Stokes transport calculus uses independent
coordinates. Scale changes commute thru extension weight **including L**.
Landau proof needs mean-free vs based map for C, not changing action. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Odom
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Inlay Inlay.Net Lattice
variable {X R : Type*}{n : Side}(G:Gauge){Y:Type*}

lemma extra_silver (x: Site n): (silver n).extra ((silver n).pick x).val= (silver n).extra x:=by
  rcases (silver n).split x with hx|hx; change (silver n).extra ((silver n).chief x)=_; rw [hx]; change (silver n).extra ((silver n).chief x)=_; rw [hx]; simp [silver,Token.extra, eq_comm] -- neg eq symmetry
lemma meetsQ (h:Even n.val)(b:Bool): Receipt.Meets (walkT n G b) (1/2):=by
  constructor
  · intro F; let V:=copper n; let Q := Foil n; change _ • (∑ x:Edge _, F (V.pick x))= _; rw [V.sum_groups, Finset.smul_sum]; refine Finset.sum_congr rfl fun x _=>?_ ; rw [Token.extra,if_neg (cop_nofix h _), show (2:ℕ) • F x=(2:ℝ) • F x by simp [two_smul]]; rw [smul_smul]; norm_num
  intro F; let V':= silver n; let W(x:Angle n):=(recede b x).elim 0 F
  have hu (x:Site n): (walkT n G b).rate x=(2:ℝ)/(V'.extra (V'.pick x).val):=by rw [extra_silver,walkT]; by_cases he:-x=x<;> norm_num [silver,Token.extra,he]
  simp_rw [hu]; change (1/2:ℝ) • (∑ x:Site n, ((2:ℝ)/(V'.extra (V'.pick x).val)) • W (V'.pick x))=_; rw [V'.sum_groups (fun x:V'.Qual=> ((2:ℝ)/(V'.extra x.val)) • W x), Finset.smul_sum]
  have hp (x:Angle n): (1/2:ℝ) • ((V'.extra x.val) • (((2:ℝ)/(V'.extra x.val)) • W x))= W x:=by unfold V' Token.extra; split<;> norm_num [two_smul,smul_add, ← add_smul]
  simp_rw [hp]; have hx (x:Angle n): W x= ∑ i:Nail n b, if i.val=x then F i else 0:=by
    by_cases he: selects b x; · unfold W recede; rw [dif_pos he,Finset.sum_eq_single (⟨x,he⟩:Nail n b)]; rw [if_pos rfl]; rfl; intro i hi hh; rw [if_neg]; exact fun ht=>hh (Subtype.ext ht); simp
    rw [Finset.sum_eq_zero]; unfold W recede; rw [dif_neg he]; rfl; intro i _; rw [if_neg]; intro hh; exact he (hh ▸ i.property)
  simp_rw [hx]; rw [Finset.sum_comm]; simp

abbrev Root (P: Precision.ChartRatio G)(n:Side)(b:Bool)(hp:Precision.LocalRatio P): Book (blush n b) G:= (Rack G n P hp).hoist (1/2) (walkT n G b)
lemma squall (h:Even n.val)(P:Precision.ChartRatio G)(hp:Precision.LocalRatio P)(b:Bool): Book.Unify (Rack G n P hp) (Root G P n b hp) (walkT n G b) (1/2):= Book.unity _ _ _ (meetsQ G h b)

-- compare later to alternative root prescription on unbased graph. There also want half operator lens even if omitted. Map simply drop.
def pegT (G:Gauge)(n:Side): Receipt G (blush n false) (blush n true) where
 parcel i:= i
 node i:= recede true i.val
 flip _:=false
 color:=1
 rate _:=1
 start e:= by simp [blush,slur,recede,selects]
 stop e:= by simp [blush,slur,recede,selects]
lemma echo0 (x:Site n) : (slur false x).bind (pegT G n).node= slur true x:=by unfold slur; simp [selects,recede,pegT]
lemma notches (b:Bool)(x:Site n): (slur b x).isSome ↔ b=false ∨ x≠0:=by
  let S:=silver n; have he : S.chief 0=0:= by rcases S.split 0 with h|h; exact h; exact h.trans (neg_zero)
  have ht : S.chief x=0 ↔ x=0:=by
    constructor
    · intro hx
      have hv:S.pick x=S.pick 0:=Subtype.ext (hx.trans he.symm); rcases (S.pick_eq x 0).mp hv with h|h; exact h; exact h.trans (neg_zero)
    rintro rfl; exact he
  have he: selects b ((silver n).pick x)↔ b=false ∨ x≠0:= or_congr Iff.rfl ht.not
  by_cases hh: selects b ((silver n).pick x)<;> simp [slur,recede,hh,← he]
lemma peg_unify {P:Precision.ChartRatio G} (hp:Precision.LocalRatio P) : Book.Unify (Root G P n false hp) (Root G P n true hp) (pegT G n) 1:=by
  constructor
  · constructor
    · constructor
      · intro F; rw [one_smul]; rfl
      intro F; rw [one_smul]; change (∑ x:Nail n false,(1:ℝ) • (recede true x.val).elim 0 F)=_; simp_rw [one_smul]
      have ht (x:Nail n false) : (recede true x.val).elim 0 F= ∑ i:Nail n true, if x=(⟨i.val, Or.inl rfl⟩:Nail n false) then F i else 0:=by
        by_cases he: selects true x.val
        · rw [recede,dif_pos he]; rw [Finset.sum_eq_single (⟨_,he⟩:Nail n true)]; rw [if_pos rfl]; rfl; intro i _ hi; rw [if_neg]; exact fun hp=>hi (Subtype.ext (congr_arg Subtype.val hp).symm)
          simp
        rw [Finset.sum_eq_zero]; rw [recede, dif_neg he]; rfl; intro i _; rw [if_neg]; intro hh; exact he ((congr_arg Subtype.val hh).symm ▸ i.property)
      simp_rw [ht]; rw [Finset.sum_comm]; simp
    intro U; rw [one_mul]; have he : ∀ x : Foil n,(pegT G n).react U x=U x:=by intro x; unfold Receipt.react pegT; simp
    change _=(1/2:ℝ)*Wilson.energy ((walkT n G false).react ((pegT G n).react U)); rw [funext he]; rfl
  rfl
end YM.MSBar.Odom
