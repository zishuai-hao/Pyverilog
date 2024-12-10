module top(
    input wire a,    // 输入信号
    input wire b,    // 输入信号
    output reg out   // 输出信号
);

assign out = 1'b0;

always @ (a) begin
    if (a == 1'b1) begin
        out <= b;
    end else begin
        out <= 1'b0;
    end
end

// 直接在另一个always中 或者在
always @ (b) begin
    if (b == 1'b1) begin
        out <= a;
    end else begin
        out <= 0'b0;
    end
end

endmodule