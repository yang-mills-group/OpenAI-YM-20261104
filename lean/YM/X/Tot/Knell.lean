import YM.X.Try.Aspect
/-!
# Periodic scalar measure triple from punctured integration. root spin stamp along x curve; SBP single lines included.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed
open Stems hiding X
open Ocean Haze Friend Fielding Print
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{d k m:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable (χ:Floor R)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=> epsilon q
local notation "o"=> side q k
abbrev Tops (G:Gauge):= Bone G ⊤
abbrev Marks (G:Gauge):= Stool G
def normF {T:Submodule ℝ (Fan G)} (e:ℝ)(p:Bone G T):= (e^(p.k+1))⁻¹ • p.x
def entryK (n:Side)(e:ℝ)(x:Cover)(u:Marks G)(z:Cover)(w:Tops G):ℂ:= ↑(spend n x z (normF e u) (normF e w))
lemma shift_e (x z t:Cover)(a:Marks G)(b:Tops G): entryK n e (t+x) a (t+z) b=entryK n e x a z b:= by unfold entryK; rw [spend_lead]
lemma replace_z (x z t:Cover)(h:wrap n z=wrap n t)(b:Tops G)(a:Marks G) : entryK n e x a z b= entryK n e x a t b:= by
   have he(f g:Fan G) : spend n x z f g=spend n x t f g:= by
       suffices h: spend (G:=G) n x z= spend n x t by rw [h]
       ext p r;  simp only [LinearMap.comp_apply,Finsupp.lsingle_apply]; rw [spend_single,spend_single]; unfold tau Braid.cane pointB; simp only [map_add,h]
   exact congr_arg Complex.ofReal (he ..)
lemma follow_r (x z:Cover)(f:Marks G)(v:Tops G)(ht:0<e): entryK n e x f z v= ↑(spend n x z f.x v.x /e^(2+(f.k+v.k))):= by
   unfold entryK normF; rw [map_smul,map_smul, LinearMap.smul_apply]; change ↑((e^(v.k+1))⁻¹*((e^(f.k+1))⁻¹*_) :ℝ)= (↑(_:ℝ):ℂ); rw [show 2+(f.k+v.k)=f.k+1+(v.k+1) by omega,pow_add e (f.k+1) (v.k+1)]; field_simp
lemma stamps (x z:Cover)(p:Marks G)(w:Tops G): treats (flow G n) (com (tack p.k e n x p.x)) (com (tack w.k e n z w.x))=entryK n e x p z w:= by rw [cornered, entryK,spent,normF,normF,map_smul (leadsL _),map_smul (leadsL _)];rfl
-- cone from dib relative y
variable (u:Tops G)(f:Marks G)(y:Fielding.Walk)(p:E4)(hq:1<q.val)(hp:plot q y p)
def wire (q:ℕ+)(x:Fielding.Walk)(b:Marks G)(a:Tops G)(k:ℕ)(z:Site (side q k)) :ℂ:= entryK (side q k) (epsilon q k) (x k) b (lift z) a
lemma wire_auth (z:Cover): wire q y f u k (wrap (side q k) z)=entryK o (ε k) (y k) f z u:= replace_z _ _ _ (wrap_lift _) _ _
def fromX (q:ℕ+)(x:Fielding.Walk)(f:(i:ℕ)→ Site (side q i)→ℂ): Mist ℂ:= fun k z=> f k (wrap _ (x k+z))
lemma rebaseW (x:Fielding.Walk): fromX q x (wire q y f u)= fun k z=> entryK (side q k) (epsilon q k) ((y-x) k) f z u:= by ext1 k; ext1 z; unfold fromX; rw [wire_auth,← shift_e _ z (x k)]; simp
include hp hq
lemma wire_step (x:Fielding.Walk){z:E4}(he:plot q x z)(hr:0≤r)(hx:r< ‖p-z‖): Chase q r 0 (fromX q x (wire q y f u)):= by
    let A:=fromP q f.k (y-x) f.x; let Y:= fun i:ℕ=> (epsilon q i ^ (u.k+1))⁻¹; have h: Tide q r A:= from_tide hq hr hx (plot.sub hp he) f.x f.order f.sector
    let b:= cuppa true A u.x; have ht: Chase q r (↑(u.k+1:ℕ)) (fun i z=>Complex.ofReal (b i z)):= Chase.com (Chase.root_pay hq h u.x u.order true)
    have hy: Chase q r (-(↑(u.k+1):ℤ)) (Once (fun i:ℕ=> Complex.ofReal (Y i))):= by unfold Y; simp_rw [←zpow_natCast, ← zpow_neg]; exact Chase.com (Chase.power ..)
    rw [rebaseW]; have hy':= ht.mulC hq hy; rw [add_neg_cancel] at hy'; refine Eq.mp ?_ hy'; congr 1; ext1 k; ext1 z; unfold entryK; rw [normF,normF,map_smul,map_smul, LinearMap.smul_apply]; change (b k z:ℂ)*(Y k:ℂ)= ↑((Y k)* ((epsilon q k ^(f.k+1))⁻¹*spend (side q k) ((y-x) k) z f.x u.x):ℝ); change _= Complex.ofReal (Y k* _); rw [←from_license, Complex.ofReal_mul]; exact mul_comm ..
omit hp
lemma wire_far (S: Finset I)(x:I→Fielding.Walk)(z:I→E4)(h:Apart S z R)(hx:∀ i∈S,plot q (x i) (z i)) {i:I}(hi:i∈ S): Isle q S x z χ 2 (fun y=> wire q (x i) f u y.1 (wrap _ y.2)):= by
    simp_rw [wire_auth]; rw [show (fun y:Post=> entryK _ _ (x i y.1) f y.2 u)=Crate.cross (travelers Prod.fst q G) (liftC q Prod.fst (x i) f) (Porch.pillar q u.k u.x) from funext (fun y=>(stamps (n:=side q y.1) (x i y.1) y.2 f u).symm)]; exact pole_cross hq S x z hx χ h hi u.x u.order _ (show (liftC q Prod.fst (x i) f)∈ Meter q Prod.fst (x i) G from ⟨_,rfl⟩) -- yields at stitches treats marker,defeq after stamps
end YM.PositionX.Tot
