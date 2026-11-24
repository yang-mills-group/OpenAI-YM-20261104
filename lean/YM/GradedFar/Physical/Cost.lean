import YM.GradedFar.Physical.Sector

/-!
# (G.6) buy `D` even when B is not yet chosen
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open Scale Dframe
open OPE Orbits Logged OPE.Logged.Deck Horizon
open OPE.Log (badge)
open Economy (Paint)
open Continuation
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G

-- Weights used for spatial price (no B).
lemma badge_tariff (simple:G.Simple) : ∃ C:ℝ,0<C ∧ ∀ᶠ r in τ,badge r ≤ C*gYM G r ^(-(2:ℝ)) := by
   let D:=G.slopeConstant
   have hd:0<D:= Gauge.slopeConstant_pos simple
   refine ⟨1+D⁻¹,by positivity,?_⟩
   filter_upwards [(log_kinetic simple).eventually_ge_atTop (1:ℝ)] with r (h : 1 ≤ D*Real.log r⁻¹)
   let x:=Real.log r⁻¹; have ht:0<D*x:=zero_lt_one.trans_le h
   rw [log_cost]; change 1+x ≤ (1+D⁻¹)*g r^(_)
   have hz : g r^(-(2:ℝ))= D*x := by
     change (√(D*x))⁻¹^(-(2:ℝ))=_
     rw [Real.inv_rpow (Real.sqrt_nonneg _),Real.rpow_neg (Real.sqrt_nonneg _),inv_inv]
     exact (Real.rpow_two _).trans (Real.sq_sqrt ht.le)
   rw [hz,add_mul,one_mul, ← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]; gcongr

lemma flagged (simple:G.Simple) {D : Economy.Small I} {x f:I→ℝ} (h:Paint D f x) :
    ∀ᶠ n:ℝ in atTop, ∃ C:ℝ,0<C ∧ ∀ᶠ i in D.p,x i ≤ C*gYM G (D.r i)^(-n)*|f i| := by
    obtain ⟨c,hc,k,h⟩:=h; obtain ⟨C,hC,hx⟩:=badge_tariff simple
    filter_upwards [eventually_ge_atTop (2*(k:ℝ))] with n hn
    refine ⟨c*C^k,mul_pos hc (pow_pos hC _),?_⟩
    filter_upwards [h,D.ran,D.leaps.eventually hx,D.leaps.eventually (positive_g simple),
      D.leaps.eventually ((shrink simple).eventually_lt_const zero_lt_one)] with i h hu hh hx hp
    rw [Real.norm_eq_abs] at h
    apply ((le_abs_self _).trans h).trans; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hw:0<badge (D.r i):=zero_lt_one.trans_le hu
    calc
        _ ≤ c*(C*g (D.r i)^(-(2:ℝ)))^k := by gcongr
        _ = c*C^k*g (D.r i)^(-(2:ℝ)*(k:ℝ)):= by rw [Real.rpow_mul hx.le,mul_pow,Real.rpow_natCast,mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx hp.le (by linarith only [hn])) (by positivity)
section
variable (D : Deck.Pitch I) (u:I→Inputs G d)(v:I→Inputs G e)
variable {C C' M' δ:ℝ}(hm:0 ≤ M')(hδ:0<δ)(x:I→Points n)(y:I→Points m)(o:I→View U)
    (hl:∀ᶠ i in D.p,Terracing (D.r i) (D.s i) M' δ (x i) (y i))
    (hu:∀ᶠ i in D.p,Within C (u i))(hv:∀ᶠ i in D.p,Within C' (v i))
    (hc:LogTrace U Q.port)
include H hq he hm hδ hl hu hv hc
/-- Compact notation for (G.6) on (d,e,h), the real radii and unit-ball inputs. D operator
in dual basis/weigh norm, and point estimate at corresponding arbitrary unit input.
Read exactly on these fields (see `Legs.receive_leg` using `w.len=r,w.Coarse=s`). -/
def Owed (k C : ℝ) (h : ℕ)(r s:ℝ)(o:View U)(x:Points n)(y:Points m)(u:Inputs G d)(v:Inputs G e)(a:Sec G h) :=
     let T i:=Yactual U K r s i x y u v
     let V:=packet U K Q d h r o x u
     let D' i (a:Sec G h):=Dactual U K r s i y v a
     let E (b:Sec G h):=D' o b-D' (none,o.2) b
     let X:=C*g r^(-k)
     ‖T o-D' o V‖ ≤ X*(s+(r/s)^(h+1)) ∧
      ‖T o‖+‖chair G h V‖+‖D' o a‖+weigh h (D' o) ≤ X ∧
      ‖T o-T (none,o.2)‖+‖E a‖+weigh h E ≤ X*s
lemma rooms (h:ℕ)(a:I→Sec G h)(ha:∀ᶠ i in D.p,Ball 1 (a i)) :
    ∀ᶠ k:ℝ in atTop,∃ C:ℝ,0<C ∧ ∀ᶠ i in D.p,Owed U Q K k C h (D.r i) (D.s i) (o i) (x i) (y i) (u i) (v i) (a i) := by
   let T (i:I) q:= Yactual U K (D.r i) (D.s i) q (x i) (y i) (u i) (v i)
   let R' i q (a:Sec G h):= Dactual U K (D.r i) (D.s i) q (y i) (v i) a
   let E (i:I)(b:Sec G h):= R' i (o i) b-R' i (none,(o i).2) b
   have he0 (b:Toon G h): Paint D.toSmall D.s (fun i=> E i (theory b)) ∧ Paint D.toSmall (fun i=>1+Deck.radius D h i)
        (fun i=> R' i (o i) (theory b)) := response_value N M H U Q J K θ hq he D v hm hδ x y o hl hv hc _ 1 (Eventually.of_forall fun _=> ball_basis b)
   obtain ⟨h1,h2,h3⟩:= mixed_story N M H U Q J K θ hq he D u v hm hδ x y o hl hu hv hc h
   have h4 := packet_fee (h:=h) N M H U Q J K θ hq he D u hm hδ x y o hl hu hc
   obtain ⟨h6,h5⟩:= response_value N M H U Q J K θ hq he D v hm hδ x y o hl hv hc a 1 ha
   have h7 : Paint D.toSmall D.s (fun i=> weigh h (E i)):= Paint.sum Finset.univ (fun j _=> (he0 j).1.norm)
   have h8 : Paint D.toSmall (fun i=>1+Deck.radius D h i) (fun i=> weigh h (R' i (o i))) := Paint.sum Finset.univ (fun j _=> (he0 j).2.norm)
   have ht : ∀ᶠ i in D.p,0≤Deck.radius D h i ∧ Deck.radius D h i ≤ 2:= by
      filter_upwards [D.outer.bounded,D.toSmall.positive,D.cost] with i (hq:D.s i≤1) (hr:0 < D.r i) hp
      have hu:= hr.trans_le hp
      unfold Deck.radius; constructor
      · positivity
      have hh:(D.r i/D.s i)^(h+1) ≤ 1:=pow_le_one₀ (by positivity) ((div_le_one hu).mpr hp)
      linarith only [hh,hq]
   have h9 : ∀ᶠ i in D.p, |(1:ℝ)| ≤ |1+Deck.radius D h i|:= ht.mono (fun i h=> (by
      rw [abs_one]; apply (le_add_of_nonneg_right h.1).trans; exact le_abs_self _))
   filter_upwards [flagged simple h1.norm,flagged simple (((h3.norm.plus (h4.norm.eases (U:=fun i=> 1+Deck.radius D h i) h9)).plus h5.norm).plus h8),
     flagged simple ((h2.norm.plus h6.norm).plus h7)] with k ⟨c0,hu,hφ⟩ ⟨c1,hv,hψ⟩ ⟨c2,hw,hπ⟩
   refine ⟨c0+3*c1+c2,by positivity,?_⟩
   filter_upwards [hφ,hψ,hπ,D.outer.positive,ht,D.leaps.eventually (positive_g simple)] with i hφ hψ hπ hi ht hg
   let W:= Deck.radius D h i
   have hz:0<g (D.r i)^(-k):= Real.rpow_pos_of_pos hg _
   rw [abs_of_nonneg ht.1] at hφ; rw [abs_of_nonneg (add_nonneg zero_le_one ht.1)] at hψ; rw [abs_of_nonneg (show 0≤D.s i from hi.le)] at hπ
   unfold Owed
   refine ⟨?_,?_,?_⟩
   · refine hφ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hz.le) ht.1); linarith only [hu,hv,hw]
   · refine hψ.trans ?_
     apply le_trans (mul_le_mul_of_nonneg_left (show 1+W ≤ 3 from by have hh:W≤2:=ht.2; linarith only [hh]) (show 0 ≤ c1*g (D.r i)^(-k) from (mul_pos hv hz).le))
     calc
       _ = (3*c1)*g (D.r i)^(-k) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hu,hv,hw]) hz.le
   · exact hπ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hu,hv,hw]) hz.le) (show 0≤D.s i from hi.le))
end
end
end YM.FVA2.GradedFar.Physical
