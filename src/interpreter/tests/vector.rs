#[test]
#[allow(non_snake_case)]
#[ignore] // This is an aspirational test, we don't have everyhting we need for it yet
fn vector_push_and_get() {
    crate::assert_ok!(
        {
            // Vec class and test code goes here
            class Vec[type T] {
                array: Array[T];
                length: Int;

                fn push(mut self, value: given T) -> () {
                    let new_length = self.length.ref + 1;
                    if new_length >= array_capacity[T, ref[self.array]](self.array.ref) {
                        let new_capacity = self.length * 2;
                        let new_array = array_new[T](new_capacity.ref);
                        array_move_elements[T](new_array.mut, self.array.mut, self.length.ref);
                        self.array = new_array.give;
                    }

                    array_write[T, mut[self.array]](self.array.mut, self.length.ref, value);
                    self.length = new_length;
                }

                fn get[perm P](P self, index: Int) -> given[self] T {
                    if index < 0 || index >= self.length.ref {
                        !
                    }
                    array_give[T, given, given](self.array.give, index)
                }
            }

            class Data {
                value: Int;
            }

            class Main {
                fn main(given self) -> () {
                    let v = new Vec[Data](array_new[Data](1), 0);
                    v.push(new Data(10));
                    print(v.ref);
                    v.push(new Data(20));
                    v.push(new Data(30));
                    v.push(new Data(40));
                    print(v.ref);
                }
            }
        }
    );
}
