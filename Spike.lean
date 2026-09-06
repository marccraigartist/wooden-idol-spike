import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Incompleteness.Löb
import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.Tarski
import Foundation.FirstOrder.Incompleteness.Examples

open LO.FirstOrder Arithmetic

#check consistent_unprovable 𝗜𝚺₁
#print axioms consistent_unprovable
#check @löb_theorem
#print axioms löb_theorem
#check @formalized_löb_theorem
#check @LO.FirstOrder.Arithmetic.fixedpoint
#check @LO.FirstOrder.Arithmetic.diagonal
#check @undefinability_of_truth
#print axioms undefinability_of_truth
#check (𝗜𝚺₁).consistent.val
#check @RobinsonQ
