import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.io.InputStream;

import javax.imageio.ImageIO;
import javax.swing.JPanel;

/**
 * @author Oliver Brausch 25.11.2009
 */
public class Piece extends JPanel {
	private static final long serialVersionUID = 1L;
	private BufferedImage img = null;
	char type;
	int col;
	int row;

	public Piece(char type, int col, int row) {
		this.type = type;
		this.col = col;
		this.row = row;
		this.setBounds(col*70, (7-row)*70);
		
		String color = Character.isUpperCase(type) ? "W" : "b";
		String image = "res/" + color + String.valueOf(type) + ".png";
		
		try {
			InputStream is = getClass().getResourceAsStream(image);
			this.img = ImageIO.read(is);
		} catch (Exception io) {
			io.printStackTrace();
		}
	}
	
	public boolean isThere(int testcol, int testrow) {
		return testcol == col && testrow == row;
	}
	
	public void setBounds(int x, int y) {
		super.setBounds(x, y, 70, 70);
	}
	
	public void paintComponent(Graphics g) {
		if (this.img != null) g.drawImage(this.img, 0, 0, this);
	}	
}
