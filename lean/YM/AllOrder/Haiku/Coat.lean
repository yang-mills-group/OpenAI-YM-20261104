import YM.AllOrder.Haiku.Vertex
import YM.AllOrder.Haiku.Ether
import YM.AllOrder.Haiku.Projection
import YM.Next.STATIONARY.Shape.ClassicalMatch
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Coat
open Project PertExtension.Series Radial Ink.Money
-- Programs across any mesh.
structure PictureT {ι:Type} (Λ:ι→ℝ)(F:ι→Ink.Money.Bills (Coarse G))(k:ℕ) where
 shape : ι→Picture G k
 heigh:ℝ
 fee:ι→ℝ
 pos:0<heigh
 bill: Grade Λ fee
 price:∀ i j k0,Firm heigh (fee i) (shape i j k0)
 period:∀ i n,Recorded (shape i) (F i n) 0
abbrev Ready (Λ:ι→ℝ)(F:ι→Ink.Money.Bills (Coarse G))(k:ℕ):Prop:= Nonempty (PictureT Λ F k)

variable {F G':ι→Ink.Money.Bills (Coarse G)} {Λ : ι→ℝ}
lemma no_charge (f : Link G n→ℝ)(h: iteratedFDeriv ℝ (k+1) f 0=0): Recorded (0:Picture G k) f 0:= by
   refine (record_exact ..).2 (fun i _ _=>?_); unfold collected noteAt beat; rw [h]; simp only [Pi.zero_apply,mul_zero,ite_self,_root_.smul_apply]; rw [enlarge,recording_apply]; simp
lemma remake {g: Picture G k} (u v:Link G n→ℝ) (he: iteratedFDeriv ℝ (k+1) u 0=iteratedFDeriv ℝ (k+1) v 0) (h:Recorded g u 0): Recorded g v 0:= by intro p i b; unfold noteAt beat; rw [← he]; exact h ..

lemma Ready.nought (F:ι→Ink.Money.Bills (Coarse G))(Λ:ι→ℝ) (h:∀ i n,iteratedFDeriv ℝ (k+1) (F i n) 0=0):Ready Λ F k:= ⟨0,1,0,zero_lt_one,gia _ le_rfl,fun _ _ _=>Firm.zero zero_lt_one,fun i n=> no_charge _ (h i n)⟩
lemma Ready.lined (h:Ready Λ F k)(he : ∀ i n,iteratedFDeriv ℝ (k+1) (F i n) 0=iteratedFDeriv ℝ (k+1) (G' i n) 0):Ready Λ G' k:=by
 rcases h with ⟨A⟩; exact ⟨{ A with period:= fun i n=> remake _ _ (he i n) (A.period i n) }⟩
lemma Ready.joint (h:Ready Λ F k)(H:Ready Λ G' k)(he:∀ i n,AnalyticAt ℝ (F i n) 0)(hv:∀ i n,AnalyticAt ℝ (G' i n) 0): Ready Λ (fun i n=> F i n - G' i n) k ∧ Ready Λ (fun i n=> F i n+G' i n) k := by
 rcases h with ⟨A⟩; rcases H with ⟨B⟩; let C:=min A.heigh B.heigh; let G:=fun i=> A.fee i+B.fee i; let ht:=A.bill.add B.bill; have hc:0<C:= lt_min A.pos B.pos; have hx (i j k):= (A.price i j k).mono hc (min_le_left ..) le_rfl; have hq(i j k):=(B.price i j k).mono hc (min_le_right ..) le_rfl; exact ⟨⟨fun i=> A.shape i-B.shape i,C,G,hc,ht,fun i j k=> (hx i j k).sub (hq i j k), fun i n=> (A.period i n).less (he i n) (hv i n) (B.period i n)⟩,⟨fun i=> A.shape i+B.shape i,C,G,hc,ht,fun i j k=> (hx i j k).add (hq i j k), fun i n=> (A.period i n).both (he i n) (hv i n) (B.period i n)⟩⟩
-- for arbitrary price post-L Ω. rank at least 1 (cost vanish rank1 later).
variable [Nonempty ι] {A:ι→Ink.Field (Coarse G)} {G₁:ι→ℝ} (hG:Grade Λ G₁) (ha:0<a)(hA:∀i,(A i).Good a (G₁ i) k)
include hA hG ha
lemma Ready.path (N:ℕ): Ready Λ (fun i n=> (A i).table n) N:= by
 let t(i:ι):= (A i).table; choose f hf h using fun i=> Revenue.rent_coin (A i) (hA i) ha (N:=N); let s:= weaker (N+1) (Rail.widthG a (N+1)); have hs:0<s:= Rail.shorter _ (hA (Classical.arbitrary _)) ha _
 let c:= (‖(↑(Nat.factorial (N+1)):ℂ)⁻¹‖); let Ω:= Rail.mantle (N+1) k; let D:=countCost (Rail.widthG a (N+1) /2); let Z(i):= c* ((Ω*G₁ i) * D* boltC N s)
 refine ⟨f,small_a s,Z,(by apply div_pos hs; norm_num), ?_,hf,h⟩; exact (gia c (norm_nonneg _)).mul ((((gia Ω (Rail.mantle_pos _ _).le).mul hG).mul (gia D (count_pos (half_pos (Rail.widthG_pos ha))).le)).mul (gia (boltC N s) (boltC_pos N hs).le))
end Coat
end YM.AllOrder.Haiku
